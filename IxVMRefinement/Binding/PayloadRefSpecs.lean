import IxVMRefinement.Binding.PayloadCoreSpecs
import IxVMRefinement.Binding.FamilyAdmits
import IxVMRefinement.Binding.WalkReachClosed
import IxVMRefinement.Binding.PayloadDirectLoads
import IxVMRefinement.FamilyGraph.ProducersGraph
import IxVMRefinement.FamilyGraph.ProducersInner
import IxVMRefinement.FamilyGraph.AdviceChecked
import IxVMRefinement.FamilyGraph.InnerChecked
import IxVMRefinement.Assembly.FamilyArm
import IxVMRefinement.Decl.Modeled
import IxVMRefinement.Decl.ModeledRules
import IxVMRefinement.Claim.Decode
import IxVMRefinement.Claim.RefSafetyExcept
import IxVMRefinement.Claim.TopWalkCheck
import IxVMRefinement.Callees.ProjAddr
import IxVMRefinement.Callees.PutConstant
import IxVMRefinement.RoleVal.GroupAdmit
import IxVMRefinement.Obs.KernelDefEq3

/-! # Reference and witness specifications of `KernelModeled::check_family`

Reads every witness, advice-reference, container-reference, and family-reference guard inside an
observed `KernelModeled::check_family` call (`FamilyCallOwn`), producing the structured dependency
facts used by the payload closure (`Binding/PayloadClosed.lean`) and payload ranking
(`Binding/PayloadRanked.lean`) proofs:

* `PathPos`: non-empty dependency paths (`≥ 1` steps of `PathStep`), closed under any used-closed
  sub-store (`pathReach_closed_of_usedClosed`) and strictly decreasing `walkRank` on new nodes
  (`pathPos_walkRank_lt`).
* `get_count_spec`, `walk_path_spec`, `walk_from_block_spec`: unconditional `PathPos` reachability
  from the starting block to the stop of `walk_from_block`, preserving `L1.Stream`.
* `check_witness_spec`, `check_witnesses_spec`, `DirectContWitness.extract`, `DirectContOwn.spec`,
  `AdviceListedIn.toAdviceIn`: 4-kind witness classification, `OpOrderedAt` on every witness, and
  exact correspondence between kind-2 witnesses and `DirectContOwn`.
* `used_ref_has_spec`, `is_projection_of_spec`, `ref_projects_from_spec`,
  `projection_of_ref_block_spec`, `projection_of_advice_spec`: reference-guard helpers.
* `family_refs_ok_spec`, `check_advice_records_indexed_spec`, `container_recs_refs_spec`,
  `FamilyCallOwn.unpack`: complete reference, safety, ordering, and check specifications for the
  family record, every indexed advice record, and every container recursor. -/

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

/-! ## Non-empty dependency paths and walk-rank monotonicity -/

/-- **A non-empty dependency path** (`≥ 1` steps of `PathStep` from `a` to `b`). -/
def PathPos (E₀ : Ixon.Env) (a b : _root_.Address) : Prop :=
  ∃ m, PathStep E₀ a m ∧ PathReach E₀ m b

theorem PathReach.single {E₀ : Ixon.Env} {a b : _root_.Address} (hs : PathStep E₀ a b) :
    PathReach E₀ a b :=
  .tail .refl hs

theorem PathReach.trans {E₀ : Ixon.Env} {a b c : _root_.Address}
    (h1 : PathReach E₀ a b) (h2 : PathReach E₀ b c) : PathReach E₀ a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hs ih => exact .tail ih hs

theorem PathPos.toReach {E₀ : Ixon.Env} {a b : _root_.Address} (h : PathPos E₀ a b) :
    PathReach E₀ a b := by
  obtain ⟨m, hm, hr⟩ := h
  exact (PathReach.single hm).trans hr

theorem PathPos.single {E₀ : Ixon.Env} {a b : _root_.Address} (hs : PathStep E₀ a b) :
    PathPos E₀ a b :=
  ⟨b, hs, .refl⟩

theorem PathPos.tail {E₀ : Ixon.Env} {a b c : _root_.Address}
    (hp : PathPos E₀ a b) (hs : PathStep E₀ b c) : PathPos E₀ a c := by
  obtain ⟨m, hm, hr⟩ := hp
  exact ⟨m, hm, .tail hr hs⟩

theorem PathPos.trans_reach {E₀ : Ixon.Env} {a b c : _root_.Address}
    (h1 : PathPos E₀ a b) (h2 : PathReach E₀ b c) : PathPos E₀ a c := by
  obtain ⟨m, hm, hr⟩ := h1
  exact ⟨m, hm, hr.trans h2⟩

theorem PathPos.reach_trans {E₀ : Ixon.Env} {a b c : _root_.Address}
    (h1 : PathReach E₀ a b) (h2 : PathPos E₀ b c) : PathPos E₀ a c := by
  induction h1 with
  | refl => exact h2
  | @tail x y _ hs ih =>
    exact ih ⟨y, hs, h2.toReach⟩

/-- **Closure of `GroupReach g ∨ stored R` along `PathReach`**: given any used-closed sub-store
`R` of `E₀` that already holds all `AlreadyStoredRole t g` addresses, `PathReach` from a node
that is either `GroupReach g` or stored in `R` stays in `GroupReach g ∨ stored R`. -/
theorem pathReach_closed_of_usedClosed {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env} {g : Nat}
    (hsub : ∀ x c, recordOf R x = some c → recordOf E₀ x = some c)
    (hcl : UsedClosed R)
    (halr : ∀ x, AlreadyStoredRole t g x → (recordOf R x).isSome = true)
    {a b : _root_.Address}
    (ha : GroupReach t E₀ g a ∨ (recordOf R a).isSome = true)
    (hp : PathReach E₀ a b) :
    GroupReach t E₀ g b ∨ (recordOf R b).isSome = true := by
  induction hp with
  | refl => exact ha
  | @tail x y _ hs ih =>
    rcases ih with hrx | hsx
    · rcases hs with hu | ⟨cx, hcx, hpr, rfl⟩
      · by_cases hst : AlreadyStoredRole t g y
        · exact Or.inr (halr y hst)
        · exact Or.inl (GroupReach.ref hrx hu hst)
      · exact Or.inl (GroupReach.owner hrx hcx hpr)
    · exact Or.inr (pathReach_stored_of_usedClosed hsub hcl hsx (PathReach.single hs))

/-- **A single `PathStep` to an unstored node from a `GroupReach g` node stays `GroupReach g` and
strictly decreases `walkRank`.** -/
theorem pathStep_walkRank_lt {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env} {g : Nat}
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs)
    (halr : ∀ x, AlreadyStoredRole t g x → (recordOf R x).isSome = true)
    {a b : _root_.Address} (ha : GroupReach t E₀ g a) (hs : PathStep E₀ a b)
    (hnb : recordOf R b = none) :
    GroupReach t E₀ g b ∧ walkRank recs b < walkRank recs a := by
  have hl := ha.listed hH hw
  rcases hs with hu | ⟨ca, hca, hpr, rfl⟩
  · have hnot : ¬ AlreadyStoredRole t g b := by
      intro hst
      have hs := halr b hst
      rw [hnb] at hs
      cases hs
    obtain ⟨ca, i, hca, hi, hb⟩ := hu
    exact ⟨GroupReach.ref ha ⟨ca, i, hca, hi, hb⟩ hnot,
      walkRank_used_lt hH hw hl hca hi hb (AlreadyStoredRole.not_covered hnot)⟩
  · exact ⟨GroupReach.owner ha hca hpr, walkRank_owner_lt hH hw hl hca hpr⟩

/-- **A non-empty dependency path from a `GroupReach g` node to an unstored node stays in
`GroupReach g` and strictly decreases `walkRank`.** -/
theorem pathPos_walkRank_lt {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env} {g : Nat}
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs)
    (hsub : ∀ x c, recordOf R x = some c → recordOf E₀ x = some c)
    (hcl : UsedClosed R)
    (halr : ∀ x, AlreadyStoredRole t g x → (recordOf R x).isSome = true)
    {a b : _root_.Address} (ha : GroupReach t E₀ g a) (hp : PathPos E₀ a b)
    (hnb : recordOf R b = none) :
    GroupReach t E₀ g b ∧ walkRank recs b < walkRank recs a := by
  obtain ⟨m, hm, hr⟩ := hp
  have hnm : recordOf R m = none := by
    cases hrm : recordOf R m with
    | none => rfl
    | some cm =>
      have hsb := pathReach_stored_of_usedClosed hsub hcl (by rw [hrm]; rfl) hr
      rw [hnb] at hsb
      cases hsb
  obtain ⟨hrm, hltm⟩ := pathStep_walkRank_lt hH hw halr ha hm hnm
  suffices ∀ {x y : _root_.Address}, PathReach E₀ x y → GroupReach t E₀ g x →
      recordOf R y = none → GroupReach t E₀ g y ∧ walkRank recs y ≤ walkRank recs x by
    obtain ⟨hrb, hle⟩ := this hr hrm hnb
    exact ⟨hrb, Nat.lt_of_le_of_lt hle hltm⟩
  intro x y hxy hrx hny
  induction hxy with
  | refl => exact ⟨hrx, Nat.le_refl _⟩
  | @tail u v huv hst ih =>
    have hnu : recordOf R u = none := by
      cases hru : recordOf R u with
      | none => rfl
      | some cu =>
        have hsv := pathReach_stored_of_usedClosed hsub hcl (by rw [hru]; rfl)
          (PathReach.single hst)
        rw [hny] at hsv
        cases hsv
    obtain ⟨hru, hleu⟩ := ih hnu
    obtain ⟨hrv, hltv⟩ := pathStep_walkRank_lt hH hw halr hru hst hny
    exact ⟨hrv, Nat.le_trans (Nat.le_of_lt hltv) hleu⟩

/-! ## Common helpers -/

private theorem refs_small_of_decoded {bytes : ByteArray} {c : Ixon.Constant}
    (hsz : bytes.size < 4294967296) (he : Ixon.deConstantExact bytes = .ok c) :
    c.refs.size < 8589934592 := by
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound bytes c he
  have hrefs : c.refs.size ≤ c.resourceSize := by
    dsimp [Ixon.Constant.resourceSize]
    omega
  omega

private def dummyScopedCtx (t : Ix.Kernel.RoleTable) : Core.ScopedCtx :=
  Core.ScopedCtx.unrestricted { E := ({} : Ixon.Env), env := default, t := t, lim := none }

private theorem zmod_val_sub_one {x : F} (hne : x ≠ 0) :
    ZMod.val (x - 1) = ZMod.val x - 1 := by
  have hpos : 0 < ZMod.val x := by
    by_contra h0
    have hv : ZMod.val x = 0 := by omega
    exact hne (by simpa [hv] using (ZMod.natCast_zmod_val x).symm)
  have hlt : ZMod.val x - 1 < U32.Goldilocks.modulus :=
    Nat.lt_of_le_of_lt (Nat.sub_le (ZMod.val x) 1) (ZMod.val_lt x)
  have heq : ((ZMod.val x - 1 : Nat) : F) = x - 1 := by
    rw [Nat.cast_sub hpos, Nat.cast_one, ZMod.natCast_zmod_val]
  rw [← heq]
  exact ZMod.val_natCast_of_lt hlt

/-- **`KernelModeled::projection_block`** on a `Claim.RepConstant`: leaves the heap unchanged,
implies `IsProj c`, and returns `ownerOf a c` with its `Bytes.Address` witness. -/
private theorem projection_block_claim_spec {c : Ixon.Constant} {a : _root_.Address}
    {x_c r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrep : Claim.RepConstant h c x_c)
    (ev : ObsFn Obs.W "KernelModeled::projection_block" [x_c] h r h' cs) :
    h' = h ∧ IsProj c ∧
      ∃ b_own : Bytes.Address, Bytes.RepAddressRef Core.addrTy h' b_own r ∧
        Core.ixAddr b_own = Ix.Cert.ownerOf a c := by
  obtain ⟨infoVal, _, _, _, _, hc_eq, hinfoRep, -, -, -, -⟩ := hrep
  match Obs.«KernelModeled::projection_block».obs ev with
  | .IPrj (hv15 := hv) (he95 := hr) (he96 := hh) .. =>
    subst hh hr
    have e := (List.cons.inj (Value.construct.inj (hc_eq.symm.trans hv)).2.2).1
    cases hci : c.info <;> rw [hci] at hinfoRep <;>
      obtain ⟨_, hv', hsub⟩ := hinfoRep <;> rw [e] at hv' <;>
      try exact absurd (Value.construct.inj hv').2.1 (by decide)
    have hpv := (List.cons.inj (Value.construct.inj hv').2.2).1
    obtain ⟨blkPtr, hmk, b_own, hrepB, hix⟩ := hsub
    rw [← hpv] at hmk
    have hblk := (List.cons.inj (List.cons.inj (Value.construct.inj hmk).2.2).2).1
    subst hblk
    exact ⟨rfl, Or.inr (Or.inl ⟨_, hci⟩), b_own, hrepB, by simp [Ix.Cert.ownerOf, hci, hix]⟩
  | .CPrj (hv15 := hv) (he145 := hr) (he146 := hh) .. =>
    subst hh hr
    have e := (List.cons.inj (Value.construct.inj (hc_eq.symm.trans hv)).2.2).1
    cases hci : c.info <;> rw [hci] at hinfoRep <;>
      obtain ⟨_, hv', hsub⟩ := hinfoRep <;> rw [e] at hv' <;>
      try exact absurd (Value.construct.inj hv').2.1 (by decide)
    have hpv := (List.cons.inj (Value.construct.inj hv').2.2).1
    obtain ⟨blkPtr, hmk, b_own, hrepB, hix⟩ := hsub
    rw [← hpv] at hmk
    have hblk := (List.cons.inj (List.cons.inj (List.cons.inj
      (Value.construct.inj hmk).2.2).2).2).1
    subst hblk
    exact ⟨rfl, Or.inr (Or.inr (Or.inl ⟨_, hci⟩)), b_own, hrepB, by simp [Ix.Cert.ownerOf, hci, hix]⟩
  | .RPrj (hv15 := hv) (he189 := hr) (he190 := hh) .. =>
    subst hh hr
    have e := (List.cons.inj (Value.construct.inj (hc_eq.symm.trans hv)).2.2).1
    cases hci : c.info <;> rw [hci] at hinfoRep <;>
      obtain ⟨_, hv', hsub⟩ := hinfoRep <;> rw [e] at hv' <;>
      try exact absurd (Value.construct.inj hv').2.1 (by decide)
    have hpv := (List.cons.inj (Value.construct.inj hv').2.2).1
    obtain ⟨blkPtr, hmk, b_own, hrepB, hix⟩ := hsub
    rw [← hpv] at hmk
    have hblk := (List.cons.inj (List.cons.inj (Value.construct.inj hmk).2.2).2).1
    subst hblk
    exact ⟨rfl, Or.inr (Or.inr (Or.inr ⟨_, hci⟩)), b_own, hrepB, by simp [Ix.Cert.ownerOf, hci, hix]⟩
  | .DPrj (hv15 := hv) (he233 := hr) (he234 := hh) .. =>
    subst hh hr
    have e := (List.cons.inj (Value.construct.inj (hc_eq.symm.trans hv)).2.2).1
    cases hci : c.info <;> rw [hci] at hinfoRep <;>
      obtain ⟨_, hv', hsub⟩ := hinfoRep <;> rw [e] at hv' <;>
      try exact absurd (Value.construct.inj hv').2.1 (by decide)
    have hpv := (List.cons.inj (Value.construct.inj hv').2.2).1
    obtain ⟨blkPtr, hmk, b_own, hrepB, hix⟩ := hsub
    rw [← hpv] at hmk
    have hblk := (List.cons.inj (List.cons.inj (Value.construct.inj hmk).2.2).2).1
    subst hblk
    exact ⟨rfl, Or.inl ⟨_, hci⟩, b_own, hrepB, by simp [Ix.Cert.ownerOf, hci, hix]⟩

/-! ## `get_count`, `walk_path`, and `walk_from_block` -/

/-- **`KernelModeled::get_count`**: reads a bounded natural count `< 2^56` off an `L1.Stream`,
leaving the heap unchanged and returning the remaining stream. -/
theorem get_count_spec {x_s x_n x_s' : SourceValue F} {bytes : List UInt8}
    {h h' : Heap F} {cs : List (Call F)}
    (hs : L1.Stream h bytes x_s)
    (ev : ObsFn Obs.W "KernelModeled::get_count" [x_s] h (.tuple [x_n, x_s']) h' cs) :
    ∃ (n : Nat) (bytes' : List UInt8),
      n < 72057594037927936 ∧ x_n = .field (n : F) ∧ L1.Stream h' bytes' x_s' ∧ h' = h := by
  match Obs.«KernelModeled::get_count».obs ev with
  | .run (m2 := m2) (x_n := x_w) (x_s2 := x_s2) (v38 := v38) (ev14 := ev14)
      (he40 := he40) (ev52 := ev52) (he68 := he68) .. =>
    obtain ⟨hm2, tg, _, restPtr, -, -, hrep, hr⟩ := TagN.getTagN0_refines hs ev14.erase
    subst hm2
    injection hr with hargs
    injection hargs with hw hrest
    injection hrest with hs2 _
    subst hw hs2
    injection he40 with hargs'
    injection hargs' with hn hs'
    injection hs' with hs'' _
    subst hn hs''
    obtain ⟨hlt, hv, hm42⟩ := Lib.u64_to_field_spec (Deserialize.repU64_u64Value m2 tg.value) ev52
    rw [he68, hm42]
    exact ⟨tg.value.toNat, _, hlt, hv, hrep, rfl⟩

/-- **`KernelModeled::walk_path`**: follows `k` steps of `PathStep` (each either `UsedRef` or
projection owner) from `b_cur` to `b_stop`, preserving `L1.Stream`. -/
theorem walk_path_spec {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀) :
    ∀ (k : Nat) {x_rc x_cur x_s x_passed x_stop x_s' x_passed' : SourceValue F}
      {nf : F} {b_cur : Bytes.Address} {bytes : List UInt8}
      {h h' : Heap F} {cs : List (Call F)},
      ZMod.val nf = k →
      Bytes.RepAddressRef Core.addrTy h b_cur x_cur →
      L1.Stream h bytes x_s →
      ObsFn Obs.W "KernelModeled::walk_path" [x_rc, x_cur, x_s, .field nf, x_passed] h
        (.tuple [x_stop, x_s', x_passed']) h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∃ (b_stop : Bytes.Address) (bytes' : List UInt8),
        Bytes.RepAddressRef Core.addrTy h' b_stop x_stop ∧
        L1.Stream h' bytes' x_s' ∧
        PathReach E₀ (Core.ixAddr b_cur) (Core.ixAddr b_stop) ∧
        (0 < k → PathPos E₀ (Core.ixAddr b_cur) (Core.ixAddr b_stop))
  | 0, x_rc, x_cur, x_s, x_passed, x_stop, x_s', x_passed', nf, b_cur, bytes, h, h', cs,
      hnf, hb, hs, ev, _ => by
    have hnf0 : nf = 0 := by simpa [hnf] using (ZMod.natCast_zmod_val nf).symm
    subst hnf0
    match Obs.«KernelModeled::walk_path».obs ev with
    | .n0 (ev_qmmrohoe := evCov) (he19 := hr) (he34 := hh) .. =>
      injection hr with hargs
      injection hargs with h1 h2
      injection h2 with h3 _
      subst h1 h3
      rw [hh]
      exact ⟨b_cur, bytes,
        Bytes.repAddressRef_heapMono₂ Core.addrTy evCov.heap_extends hb,
        L1.Stream.mono evCov.heap_extends hs,
        .refl, fun h0 => by omega⟩
    | .other (hne36 := hne) .. => exact absurd rfl hne
  | k + 1, x_rc, x_cur, x_s, x_passed, x_stop, x_s', x_passed', nf, b_cur, bytes, h, h', cs,
      hnf, hb, hs, ev, hsub => by
    have hnfne : nf ≠ 0 := by
      intro h0; subst h0; simp at hnf
    match Obs.«KernelModeled::walk_path».obs ev with
    | .n0 (hv14 := hv) .. => exact absurd (Value.field.inj hv) hnfne
    | .other (m41 := m41) (m76 := m76) (cs86 := cs86) (v75 := v75) (v276 := v276)
        (m277 := m277) (cs279 := cs279) (cs288 := cs288)
        (ev53 := evCnt) (ev88 := evLd) (sg284 := sg) (ev_kkbmepwt := evCov)
        (op_lhbokqvf := opSub) (ev290 := evRec) (hc323 := hcs) .. =>
      obtain ⟨st, bytes2, hstLt, hstEq, hs2, hm41⟩ := get_count_spec hs evCnt
      subst hstEq
      have hsub86 : ∀ cl ∈ cs86, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hsub288 : ∀ cl ∈ cs288, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hb41 : Bytes.RepAddressRef Core.addrTy m41 b_cur x_cur := by rw [hm41]; exact hb
      obtain ⟨extLd, raw, c_cur, hsz, hh, hbl, hde, hdeE, hrepC, -⟩ :=
        Claim.load_verified_constant_de ⟨b_cur, hb41, rfl⟩ evLd
      have hrec : recordOf E₀ (Core.ixAddr b_cur) = some c_cur := by
        rw [← hbl]
        exact Claim.recordOf_hashed hS hH (Core.hashed_mono hsub86 hh) hsz hde hdeE
      have hstep : ∃ b_next : Bytes.Address,
          Bytes.RepAddressRef Core.addrTy m277 b_next v276 ∧
          Heap.Extends m76 m277 ∧
          PathStep E₀ (Core.ixAddr b_cur) (Core.ixAddr b_next) := by
        match sg with
        | .n0 (hv110 := hv0) (ev116 := evPb) .. =>
          obtain ⟨-, hpr, b_own, hownRep, hownEq⟩ :=
            projection_block_claim_spec (a := Core.ixAddr b_cur) hrepC evPb
          exact ⟨b_own, hownRep, evPb.heap_extends,
            Or.inr ⟨c_cur, hrec, hpr, hownEq⟩⟩
        | .other (x_refs := x_refs) (hne126 := hne0) (hv144 := hvC)
            (ev213 := evIdxs) (op235 := op1) (ev199 := evHas) (heq243 := h1)
            (op272 := op2) (ev249 := evLk) .. =>
          have hstPos : 0 < st := by
            by_contra h0
            have hz : st = 0 := by omega
            subst hz
            exact hne0 (by simp)
          have hstSub : ((st : F) - 1) = ((st - 1 : Nat) : F) := by
            rw [Nat.cast_sub hstPos, Nat.cast_one]
          simp only [evalBinOp, Except.ok.injEq] at op1 op2
          subst op1 op2
          rw [hstSub] at evHas evLk
          obtain ⟨extIdxs, hidxsRep⟩ := Claim.const_idxs_of_spec hrepC evIdxs
          have hst1Lt : st - 1 < 72057594037927936 := by omega
          obtain ⟨hmHas, hiff⟩ := Claim.g_list_has_spec (Core.S0.usedRefIdxs c_cur) hst1Lt
            hidxsRep evHas
          have husedS0 : st - 1 ∈ Core.S0.usedRefIdxs c_cur := hiff.mp h1
          have hused : st - 1 ∈ usedRefIdxs c_cur := by
            rwa [← Assembly.usedRefIdxs_eq]
          obtain ⟨_, _, refsPtr, _, _, hmk, -, -, hrefsRep, -, -⟩ := hrepC
          rw [hvC] at hmk
          injection hmk with _ _ hargs
          simp only [List.cons.injEq] at hargs
          obtain ⟨-, -, rfl, -⟩ := hargs
          rw [hmHas] at evLk
          have hrefsRep1 := RepLinkedList.mono Claim.repAddrElem_heapMono₂ extIdxs hrefsRep
          rw [← Obs.Names.«Lists::lookup<&[Field; 32]>».symbol] at evLk
          rw [← Obs.Names.«Lists::Node<&[Field; 32]>».symbol] at hrefsRep1
          obtain ⟨⟨a_next, hget, ⟨b_next, hbNext, haNext⟩⟩, hmLk⟩ :=
            Lib.Lists.lookup_spec evLk hrefsRep1
          have hvalEq : ZMod.val ((st - 1 : Nat) : F) = st - 1 :=
            ZMod.val_natCast_of_lt (Nat.lt_trans hst1Lt (by decide))
          rw [hvalEq, Array.getElem?_toList] at hget
          rw [← haNext] at hget
          exact ⟨b_next, by rw [hmLk]; exact hbNext,
            by rw [hmLk]; exact extIdxs,
            Or.inl ⟨c_cur, st - 1, hrec, hused, hget⟩⟩
      obtain ⟨b_next, hbNext, extSg, hpathStep⟩ := hstep
      have extRec : Heap.Extends m41 _ := extLd.trans (extSg.trans evCov.heap_extends)
      simp only [evalBinOp, Except.ok.injEq] at opSub
      subst opSub
      have hvalSub : ZMod.val (nf - 1) = k := by
        rw [zmod_val_sub_one hnfne, hnf]; omega
      obtain ⟨b_stop, bytes', hbStop, hs', hreach, -⟩ :=
        walk_path_spec hS hH k hvalSub
          (Bytes.repAddressRef_heapMono₂ Core.addrTy evCov.heap_extends hbNext)
          (L1.Stream.mono extRec hs2) evRec hsub288
      exact ⟨b_stop, bytes', hbStop, hs',
        (PathReach.single hpathStep).trans hreach,
        fun _ => ⟨Core.ixAddr b_next, hpathStep, hreach⟩⟩

/-- **`KernelModeled::walk_from_block`**: takes at least one `PathStep` from `b_blk` to `b_stop`,
preserving `L1.Stream`. -/
theorem walk_from_block_spec {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {x_rc x_blk x_s x_stop x_s' x_passed : SourceValue F} {nf : F}
    {b_blk : Bytes.Address} {bytes : List UInt8} {h h' : Heap F} {cs : List (Call F)}
    (hb : Bytes.RepAddressRef Core.addrTy h b_blk x_blk)
    (hs : L1.Stream h bytes x_s)
    (ev : ObsFn Obs.W "KernelModeled::walk_from_block" [x_rc, x_blk, x_s, .field nf] h
      (.tuple [x_stop, x_s', x_passed]) h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∃ (b_stop : Bytes.Address) (bytes' : List UInt8),
      Bytes.RepAddressRef Core.addrTy h' b_stop x_stop ∧
      L1.Stream h' bytes' x_s' ∧
      PathPos E₀ (Core.ixAddr b_blk) (Core.ixAddr b_stop) := by
  match Obs.«KernelModeled::walk_from_block».obs ev with
  | .run (cs44 := cs44) (ev25 := evZ) (heq40 := hz0) (ev46 := evWp) (hc71 := hcs) .. =>
    obtain ⟨hzf, hm15⟩ := Lib.is_zero_field evZ
    have hnfne : nf ≠ 0 := by
      intro h0
      subst h0
      simp only [↓reduceIte] at hzf
      exact zero_ne_one (Value.field.inj (hz0.symm.trans hzf))
    have hpos : 0 < ZMod.val nf := by
      by_contra h0
      have hv : ZMod.val nf = 0 := by omega
      exact hnfne (by simpa [hv] using (ZMod.natCast_zmod_val nf).symm)
    have hsub44 : ∀ cl ∈ cs44, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    obtain ⟨b_stop, bytes', hbStop, hs', -, hposPath⟩ :=
      walk_path_spec hS hH (ZMod.val nf) rfl
        (by rw [hm15]; exact hb) (by rw [hm15]; exact hs) evWp hsub44
    exact ⟨b_stop, bytes', hbStop, hs', hposPath hpos⟩

/-! ## Unconditional projection hashing (`compute_iprj_addr`, `projection_addr_ctor`) -/

private theorem val_natCast_small_lt {n : Nat} (hn : n < 72057594037927936) :
    ZMod.val (n : F) = n :=
  ZMod.val_natCast_of_lt (Nat.lt_trans hn (by decide))

private theorem tag0Bytes_size_le9' (v : UInt64) :
    (Ixon.Verify.Codec.tag0Bytes v).size ≤ 9 := by
  unfold Ixon.Verify.Codec.tag0Bytes
  rw [Ixon.Verify.Codec.tagNBytes_size]
  unfold Ixon.tagNByteWidth
  repeat' split
  all_goals omega

private theorem serConstant_iprj_size_lt (i : UInt64) (b : Bytes.Address) :
    (Ixon.serConstant ⟨.iPrj ⟨i, Core.ixAddr b⟩, #[], #[], #[], #[]⟩).size < 4294967296 := by
  open Ixon.Verify.Codec Ixon.Verify.Codec.ConstantTables Ixon.Verify.Codec.NonrecursiveConstant in
  have hb : AddressWireWF (Core.ixAddr b) := b.size_toArray
  open Ixon.Verify.Codec Ixon.Verify.Codec.ConstantTables Ixon.Verify.Codec.NonrecursiveConstant in
  have hcwf : NonrecursiveConstantWireWF ⟨.iPrj ⟨i, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ :=
    { info := .iPrj hb
      sharingCount := by show (#[] : Array Ixon.Expr).size < UInt64.size; decide
      sharingEntries := by simp
      refsCount := by show (#[] : Array _root_.Address).size < UInt64.size; decide
      refsEntries := by simp
      univsCount := by show (#[] : Array Ixon.Univ).size < UInt64.size; decide
      univsEntries := by simp
      binders := by simp [Ixon.bindersWireWF] }
  open Ixon.Verify.Codec Ixon.Verify.Codec.ConstantTables Ixon.Verify.Codec.NonrecursiveConstant in
  have hser : Ixon.serConstant ⟨.iPrj ⟨i, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ =
      nonrecursiveConstantBytes ⟨.iPrj ⟨i, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ := by
    unfold Ixon.serConstant
    exact (putConstant_writes_nonrecursive _ hcwf).runPut
  open Ixon.Verify.Codec Ixon.Verify.Codec.ConstantTables Ixon.Verify.Codec.NonrecursiveConstant in
  have hbytes : nonrecursiveConstantBytes ⟨.iPrj ⟨i, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ =
      tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_IPRJ ++
        (tag0Bytes i ++ (Core.ixAddr b).hash) ++
        tag0Bytes 0 ++ ByteArray.empty ++ tag0Bytes 0 ++ ByteArray.empty ++
        tag0Bytes 0 ++ ByteArray.empty ++ bindersBytes #[] := rfl
  rw [hser, hbytes]
  have h1 := tag0Bytes_size_le9' i
  have ht4 : (Ixon.Verify.Codec.tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_IPRJ).size = 1 := by
    decide
  have ht0 : (Ixon.Verify.Codec.tag0Bytes 0).size = 1 := by decide
  have hbd0 : (Ixon.Verify.Codec.ConstantTables.bindersBytes #[]).size = 1 := by decide
  have hh : (Core.ixAddr b).hash.size = 32 := hb
  simp only [ByteArray.size_append, ByteArray.size_empty]
  omega

/-- Unconditional bytes + address specification of `KernelDefEq::compute_iprj_addr` (no `Good`). -/
theorem compute_iprj_addr_raw {t : Ix.Kernel.RoleTable} {i : F} {bp r : SourceValue F}
    {b : Bytes.Address} {h h' : Heap F} {cs : List (Call F)}
    (hb : Bytes.RepAddressRef Core.addrTy h b bp)
    (ev : ObsFn Obs.W "KernelDefEq::compute_iprj_addr" [bp, .field i] h r h' cs) :
    ∃ (a : Bytes.Address) (c_proj : Ixon.Constant),
      c_proj = ⟨.iPrj ⟨(ZMod.val i).toUInt64, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ ∧
      Bytes.RepAddressRef Core.addrTy h' a r ∧
      Core.ixAddr a = Address.blake3Pure (Ixon.serConstant c_proj) ∧
      Hashed cs (Ixon.serConstant c_proj) ∧
      c_proj.wireWF := by
  obtain ⟨v1, m2, cs12, m84, m97, m110, m123, v135, m136, cs146, m159, cs174, ev14, hm92, hm105,
    hm118, hm131, hm167, ev148, ev176, hc185⟩ := Obs.«KernelDefEq::compute_iprj_addr».obs ev
  obtain ⟨n, hn, hx, rfl, hm2⟩ := Lib.u64_from_field_spec ev14
  injection hx with hx
  have hval : ZMod.val i = n := by
    rw [hx]; exact val_natCast_small_lt hn
  have e1 : Heap.Extends m2 m84 := by rw [hm92]; exact Heap.Extends.snoc _ _
  have e2 : Heap.Extends m84 m97 := by rw [hm105]; exact Heap.Extends.snoc _ _
  have e3 : Heap.Extends m97 m110 := by rw [hm118]; exact Heap.Extends.snoc _ _
  have e4 : Heap.Extends m110 m123 := by rw [hm131]; exact Heap.Extends.snoc _ _
  have e5 : Heap.Extends m123 m159 := by rw [hm167]; exact Heap.Extends.snoc _ _
  have E : Heap.Extends h m159 := by
    rw [← hm2]; exact e1.trans (e2.trans (e3.trans (e4.trans e5)))
  have c1 : m159[m2.length]? = some (.construct Core.Specs.Callees.ixExprListEnum "Nil" []) :=
    (e2.trans (e3.trans (e4.trans e5))).getElem?_eq (by rw [hm92]; simp)
  have c2 : m159[m84.length]? = some (.construct Core.addrListEnum "Nil" []) :=
    (e3.trans (e4.trans e5)).getElem?_eq (by rw [hm105]; simp)
  have c3 : m159[m97.length]? = some (.construct Core.Specs.Callees.ixUnivListEnum "Nil" []) :=
    (e4.trans e5).getElem?_eq (by rw [hm118]; simp)
  have c4 : m159[m110.length]? = some (.construct Core.Specs.Callees.ixBinderListEnum "Nil" []) :=
    e5.getElem?_eq (by rw [hm131]; simp)
  have c5 : m159[m123.length]? = some (.construct Core.byteListEnum "Nil" []) := by
    rw [hm167]; simp
  have hrep : RepU64 m159 (ZMod.val i).toUInt64 (TagN.u64Value n) := by
    rw [hval]
    have e := Lib.repU64_ofNatLT m159 (m := n) (Nat.lt_trans hn (by decide))
    rwa [UInt64.ofNatLT_eq_ofNat] at e
  have hinfo : Core.Specs.Callees.ProjInfoRep m159 (.iPrj ⟨(ZMod.val i).toUInt64, Core.ixAddr b⟩)
      (.construct "Ixon::ConstantInfo" "IPrj"
        [.construct "Ixon::InductiveProj" "Mk" [TagN.u64Value n, bp]]) := by
    simp only [Core.Specs.Callees.ProjInfoRep]
    exact ⟨TagN.u64Value n, bp, b, rfl, hrep, Bytes.repAddressRef_heapMono₂ Core.addrTy E hb, rfl⟩
  let c_proj : Ixon.Constant :=
    ⟨.iPrj ⟨(ZMod.val i).toUInt64, Core.ixAddr b⟩, #[], #[], #[], #[]⟩
  have hbytes := Core.put_constant_step (dummyScopedCtx t) ev148 _ _
    (.iPrj ⟨(ZMod.val i).toUInt64, Core.ixAddr b⟩) [] rfl
    ⟨_, _, _, _, _, rfl, hinfo, RepLinkedList.nil c1, RepLinkedList.nil c2,
      RepLinkedList.nil c3, RepLinkedList.nil c4⟩
    (RepLinkedList.nil c5)
  rw [List.append_nil] at hbytes
  have hstream : L1.Stream m136 (Ixon.serConstant c_proj).data.toList v135 := hbytes
  obtain ⟨_, hload, hhashCall⟩ := L1.bytes_to_addr_spec hstream ev176
  let d : Bytes.Address :=
    Blake3.Pure.cvBytes (Aiur.Library.Blake3.hashModel (Ixon.serConstant c_proj).data.toList)
  have ha : Bytes.RepAddressRef Core.addrTy h' d r := Claim.repAddressRef_of_load_digestV hload
  have hnat : Blake3.Pure.NativeInput (Ixon.serConstant c_proj).data.toList := by
    show (Ixon.serConstant c_proj).data.toList.length < 2 ^ 64
    have hsz : (Ixon.serConstant c_proj).size < 2 ^ 32 :=
      serConstant_iprj_size_lt (ZMod.val i).toUInt64 b
    have hlen : (Ixon.serConstant c_proj).data.toList.length = (Ixon.serConstant c_proj).size :=
      Array.length_toList
    omega
  have hd_eq : d = Blake3.Pure.digest (Ixon.serConstant c_proj).data.toList :=
    Aiur.Library.Blake3.hash_model_spec _ hnat
  have hix : Core.ixAddr d = Address.blake3Pure (Ixon.serConstant c_proj) := by
    rw [hd_eq]
    have h1 := L1.blake3Pure_eq (Ixon.serConstant c_proj).data.toList
    simp only [Array.toArray_toList] at h1
    exact h1.symm
  have hhash : Hashed cs (Ixon.serConstant c_proj) :=
    ⟨(⟨"Blake3::hash", [v135], m136⟩ : Call F), by rw [hc185]; simp [hhashCall],
      rfl, v135, rfl, hstream⟩
  refine ⟨d, c_proj, rfl, ha, hix, hhash, ?_⟩
  have hwf := L1.projConstant_wireWF_iPrj (ZMod.val i).toUInt64 b
  simpa [c_proj] using hwf

/-- Unconditional bytes + address specification of `KernelCheck::projection_addr_ctor` (no `Good`). -/
theorem projection_addr_ctor_raw {t : Ix.Kernel.RoleTable} {i j : F} {bp r : SourceValue F}
    {b : Bytes.Address} {h h' : Heap F} {cs : List (Call F)}
    (hb : Bytes.RepAddressRef Core.addrTy h b bp)
    (ev : ObsFn Obs.W "KernelCheck::projection_addr_ctor" [.field i, .field j, bp] h r h' cs) :
    ∃ (a : Bytes.Address) (c_proj : Ixon.Constant),
      c_proj = ⟨.cPrj ⟨(ZMod.val i).toUInt64, (ZMod.val j).toUInt64, Core.ixAddr b⟩,
        #[], #[], #[], #[]⟩ ∧
      Bytes.RepAddressRef Core.addrTy h' a r ∧
      Core.ixAddr a = Address.blake3Pure (Ixon.serConstant c_proj) ∧
      Hashed cs (Ixon.serConstant c_proj) ∧
      c_proj.wireWF := by
  obtain ⟨v1, m2, cs12, v23, m24, cs34, m114, m127, m140, m153, v165, m166, cs176, m189, cs204,
    ev14, ev36, hm122, hm135, hm148, hm161, hm197, ev178, ev206, hc215⟩ :=
    Obs.«KernelCheck::projection_addr_ctor».obs ev
  obtain ⟨ni, hni, hxi, rfl, hm2⟩ := Lib.u64_from_field_spec ev14
  obtain ⟨nj, hnj, hxj, rfl, hm24⟩ := Lib.u64_from_field_spec ev36
  injection hxi with hxi
  injection hxj with hxj
  have hvali : ZMod.val i = ni := by
    rw [hxi]; exact val_natCast_small_lt hni
  have hvalj : ZMod.val j = nj := by
    rw [hxj]; exact val_natCast_small_lt hnj
  have e1 : Heap.Extends m24 m114 := by rw [hm122]; exact Heap.Extends.snoc _ _
  have e2 : Heap.Extends m114 m127 := by rw [hm135]; exact Heap.Extends.snoc _ _
  have e3 : Heap.Extends m127 m140 := by rw [hm148]; exact Heap.Extends.snoc _ _
  have e4 : Heap.Extends m140 m153 := by rw [hm161]; exact Heap.Extends.snoc _ _
  have e5 : Heap.Extends m153 m189 := by rw [hm197]; exact Heap.Extends.snoc _ _
  have E : Heap.Extends h m189 := by
    rw [← hm2, ← hm24]; exact e1.trans (e2.trans (e3.trans (e4.trans e5)))
  have c1 : m189[m24.length]? = some (.construct Core.Specs.Callees.ixExprListEnum "Nil" []) :=
    (e2.trans (e3.trans (e4.trans e5))).getElem?_eq (by rw [hm122]; simp)
  have c2 : m189[m114.length]? = some (.construct Core.addrListEnum "Nil" []) :=
    (e3.trans (e4.trans e5)).getElem?_eq (by rw [hm135]; simp)
  have c3 : m189[m127.length]? = some (.construct Core.Specs.Callees.ixUnivListEnum "Nil" []) :=
    (e4.trans e5).getElem?_eq (by rw [hm148]; simp)
  have c4 : m189[m140.length]? = some (.construct Core.Specs.Callees.ixBinderListEnum "Nil" []) :=
    e5.getElem?_eq (by rw [hm161]; simp)
  have c5 : m189[m153.length]? = some (.construct Core.byteListEnum "Nil" []) := by
    rw [hm197]; simp
  have hrepi : RepU64 m189 (ZMod.val i).toUInt64 (TagN.u64Value ni) := by
    rw [hvali]
    have e := Lib.repU64_ofNatLT m189 (m := ni) (Nat.lt_trans hni (by decide))
    rwa [UInt64.ofNatLT_eq_ofNat] at e
  have hrepj : RepU64 m189 (ZMod.val j).toUInt64 (TagN.u64Value nj) := by
    rw [hvalj]
    have e := Lib.repU64_ofNatLT m189 (m := nj) (Nat.lt_trans hnj (by decide))
    rwa [UInt64.ofNatLT_eq_ofNat] at e
  have hinfo : Core.Specs.Callees.ProjInfoRep m189
      (.cPrj ⟨(ZMod.val i).toUInt64, (ZMod.val j).toUInt64, Core.ixAddr b⟩)
      (.construct "Ixon::ConstantInfo" "CPrj"
        [.construct "Ixon::ConstructorProj" "Mk" [TagN.u64Value ni, TagN.u64Value nj, bp]]) := by
    simp only [Core.Specs.Callees.ProjInfoRep]
    exact ⟨TagN.u64Value ni, TagN.u64Value nj, bp, b, rfl, hrepi, hrepj,
      Bytes.repAddressRef_heapMono₂ Core.addrTy E hb, rfl⟩
  let c_proj : Ixon.Constant :=
    ⟨.cPrj ⟨(ZMod.val i).toUInt64, (ZMod.val j).toUInt64, Core.ixAddr b⟩, #[], #[], #[], #[]⟩
  have hbytes := Core.put_constant_step (dummyScopedCtx t) ev178 _ _
    (.cPrj ⟨(ZMod.val i).toUInt64, (ZMod.val j).toUInt64, Core.ixAddr b⟩) [] rfl
    ⟨_, _, _, _, _, rfl, hinfo, RepLinkedList.nil c1, RepLinkedList.nil c2,
      RepLinkedList.nil c3, RepLinkedList.nil c4⟩
    (RepLinkedList.nil c5)
  rw [List.append_nil] at hbytes
  have hstream : L1.Stream m166 (Ixon.serConstant c_proj).data.toList v165 := hbytes
  obtain ⟨_, hload, hhashCall⟩ := L1.bytes_to_addr_spec hstream ev206
  let d : Bytes.Address :=
    Blake3.Pure.cvBytes (Aiur.Library.Blake3.hashModel (Ixon.serConstant c_proj).data.toList)
  have ha : Bytes.RepAddressRef Core.addrTy h' d r := Claim.repAddressRef_of_load_digestV hload
  have hnat : Blake3.Pure.NativeInput (Ixon.serConstant c_proj).data.toList := by
    show (Ixon.serConstant c_proj).data.toList.length < 2 ^ 64
    have hsz : (Ixon.serConstant c_proj).size < 2 ^ 32 :=
      Claim.serConstant_cprj_size_lt (ZMod.val i).toUInt64 (ZMod.val j).toUInt64 b
    have hlen : (Ixon.serConstant c_proj).data.toList.length = (Ixon.serConstant c_proj).size :=
      Array.length_toList
    omega
  have hd_eq : d = Blake3.Pure.digest (Ixon.serConstant c_proj).data.toList :=
    Aiur.Library.Blake3.hash_model_spec _ hnat
  have hix : Core.ixAddr d = Address.blake3Pure (Ixon.serConstant c_proj) := by
    rw [hd_eq]
    have h1 := L1.blake3Pure_eq (Ixon.serConstant c_proj).data.toList
    simp only [Array.toArray_toList] at h1
    exact h1.symm
  have hhash : Hashed cs (Ixon.serConstant c_proj) :=
    ⟨(⟨"Blake3::hash", [v165], m166⟩ : Call F), by rw [hc215]; simp [hhashCall],
      rfl, v165, rfl, hstream⟩
  refine ⟨d, c_proj, rfl, ha, hix, hhash, ?_⟩
  have hwf := L1.projConstant_wireWF_cPrj (ZMod.val i).toUInt64 (ZMod.val j).toUInt64 b
  simpa [c_proj] using hwf

/-! ## Witness classification (`check_witness`, `check_witnesses`, `DirectContOwn`) -/

/-- **A checked witness's 4-kind classification** from `KernelModeled::check_witness` on `x`
for block `B` at context limit `lim`. -/
def WitnessClassified (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (lim : Option Nat)
    (B x : _root_.Address) : Prop :=
  -- Kind 0: allowed basis role (`groupOf ro < 6`, walked or quotient)
  (∃ ro : Ix.Kernel.Role, t.addressOf? ro = some x ∧
    Ix.SpecDigest.groupOf ro < 6 ∧
    (RoleVal.roleWalksBound ro = true ∨ RoleVal.isQuotRole ro = true)) ∨
  -- Kind 1: non-block stop of a positive path from `B`; if `IsProj`, member of owner & no used refs
  (PathPos E₀ B x ∧ Claim.NotBlockIn calls x ∧
    ∃ c, recordOf E₀ x = some c ∧
      (IsProj c → usedRefIdxs c = [] ∧
        ∃ cb, recordOf E₀ (Ix.Cert.ownerOf x c) = some cb ∧
          ConstAddrOf (Ix.Cert.ownerOf x c) cb x)) ∨
  -- Kind 2: container recursor of some `ib` with `PathPos E₀ B ib`
  (∃ ib, PathPos E₀ B ib ∧
    ∃ (h h' : Heap F) (rc xx xib r : SourceValue F) (cs : List (Call F)),
      Claim.RCLimRep t bAddr lim h rc ∧ Core.S0.addr h xx x ∧ Core.S0.addr h xib ib ∧
      ObsFn Obs.W "KernelModeled::check_container_rec" [rc, xx, xib] h r h' cs ∧
      (∀ cl ∈ cs, cl ∈ calls)) ∨
  -- Kind 3: `IPrj`/`CPrj` of some `ib` with `PathPos E₀ B ib`
  (∃ ib c cib, PathPos E₀ B ib ∧ recordOf E₀ x = some c ∧ IsProj c ∧
    Ix.Cert.ownerOf x c = ib ∧ usedRefIdxs c = [] ∧
    recordOf E₀ ib = some cib ∧ ConstAddrOf ib cib x)

/-- **`KernelModeled::check_witness`**: classifies the witness `x` into one of the four kinds
(tagging kind 2 with `x_kind = .field 2`) and preserves `L1.Stream`. -/
theorem check_witness_spec {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat}
    (hC : CollisionFreeRun calls E₀)
    {x_rc x_blk x_x x_kind x_s r : SourceValue F} {b_blk b_x : Bytes.Address}
    {bytes : List UInt8} {h h' : Heap F} {cs : List (Call F)}
    (hrc : Claim.RCLimRep t bAddr lim h x_rc)
    (hblk : Bytes.RepAddressRef Core.addrTy h b_blk x_blk)
    (hx : Bytes.RepAddressRef Core.addrTy h b_x x_x)
    (hs : L1.Stream h bytes x_s)
    (ev : ObsFn Obs.W "KernelModeled::check_witness" [x_rc, x_blk, x_x, x_kind, x_s] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    (∃ bytes', L1.Stream h' bytes' r) ∧
      ((∃ ro : Ix.Kernel.Role, t.addressOf? ro = some (Core.ixAddr b_x) ∧
          Ix.SpecDigest.groupOf ro < 6 ∧
          (RoleVal.roleWalksBound ro = true ∨ RoleVal.isQuotRole ro = true)) ∨
        (PathPos E₀ (Core.ixAddr b_blk) (Core.ixAddr b_x) ∧ Claim.NotBlockIn calls (Core.ixAddr b_x) ∧
          ∃ c, recordOf E₀ (Core.ixAddr b_x) = some c ∧
            (IsProj c → usedRefIdxs c = [] ∧
              ∃ cb, recordOf E₀ (Ix.Cert.ownerOf (Core.ixAddr b_x) c) = some cb ∧
                ConstAddrOf (Ix.Cert.ownerOf (Core.ixAddr b_x) c) cb (Core.ixAddr b_x))) ∨
        (x_kind = .field 2 ∧ ∃ ib, PathPos E₀ (Core.ixAddr b_blk) ib ∧
          ∃ (h₁ h₂ : Heap F) (rc₁ xx₁ xib₁ r₁ : SourceValue F) (cs₁ : List (Call F)),
            Claim.RCLimRep t bAddr lim h₁ rc₁ ∧
            Core.S0.addr h₁ xx₁ (Core.ixAddr b_x) ∧ Core.S0.addr h₁ xib₁ ib ∧
            ObsFn Obs.W "KernelModeled::check_container_rec" [rc₁, xx₁, xib₁] h₁ r₁ h₂ cs₁ ∧
            (∀ cl ∈ cs₁, cl ∈ calls)) ∨
        (∃ ib c cib, PathPos E₀ (Core.ixAddr b_blk) ib ∧
          recordOf E₀ (Core.ixAddr b_x) = some c ∧ IsProj c ∧
          Ix.Cert.ownerOf (Core.ixAddr b_x) c = ib ∧ usedRefIdxs c = [] ∧
          recordOf E₀ ib = some cib ∧ ConstAddrOf ib cib (Core.ixAddr b_x))) := by
  match Obs.«KernelModeled::check_witness».obs ev with
  | .n0 (hv14 := hk0) (ev28 := evRo) (ev69 := evZ) (heq84 := hz0) (op124 := opSub)
      (ev109 := evBas) (heq132 := hbas1) (ev146 := evRct) (he164 := hr) (he165 := hh) .. =>
    obtain ⟨extRo, hro⟩ := RoleVal.role_of_admit_spec hrc.toRCRep ⟨b_x, hx, rfl⟩ evRo
    rcases hro with hv0 | ⟨ro, hvRo, haddrRo, -⟩
    · rw [hv0] at evZ
      obtain ⟨hzf, -⟩ := Lib.is_zero_field evZ
      simp only [↓reduceIte] at hzf
      exact absurd (Value.field.inj (hz0.symm.trans hzf)) zero_ne_one
    · rw [hvRo] at opSub
      simp only [evalBinOp, add_sub_cancel_right, Except.ok.injEq] at opSub
      subst opSub
      rw [hbas1] at evBas
      obtain ⟨-, hgrp, hwk⟩ := basis_role_allowed_spec evBas rfl
      have extAll : Heap.Extends h h' := by
        rw [hh]
        exact extRo.trans (evZ.heap_extends.trans (evBas.heap_extends.trans evRct.heap_extends))
      exact ⟨⟨bytes, by rw [hr]; exact L1.Stream.mono extAll hs⟩,
        Or.inl ⟨ro, haddrRo, hgrp, hwk⟩⟩
  | .n1 (hv171 := hk1) (ev185 := evCnt) (cs_jruoheya := csW) (ev_lbttumfo := evW)
      (ev282 := evEq) (heq305 := heq1) (cs_odkbpsvr := csPm) (ev_kzxwtasl := evPm)
      (cs_pzteoqvs := csNb) (ev_scicdnpr := evNb) (cs_hblzykfb := csCi) (ev_krpcbbcl := evCi)
      (ev_mvspkqrl := evCov) (he307 := hr) (he308 := hh) (hc309 := hcs) .. =>
    obtain ⟨n, bytes2, -, hnEq, hs2, hm173⟩ := get_count_spec hs evCnt
    subst hnEq hm173
    have hsubW : ∀ cl ∈ csW, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsubPm : ∀ cl ∈ csPm, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsubNb : ∀ cl ∈ csNb, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsubCi : ∀ cl ∈ csCi, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    obtain ⟨b_stop, bytes3, hbStop, hs3, hpos⟩ :=
      walk_from_block_spec hC.runStore hC.hashedStored hblk hs2 evW hsubW
    have hxW := Bytes.repAddressRef_heapMono₂ Core.addrTy evW.heap_extends hx
    obtain ⟨heqV, hmEq⟩ := Lib.address_eq_spec evEq hbStop hxW
    have eb : b_stop = b_x := by
      by_cases hne : b_stop = b_x
      · exact hne
      · simp [hne] at heqV
        exact absurd (Value.field.inj (heqV.symm.trans heq1)) zero_ne_one
    subst eb
    have extPm : Heap.Extends _ _ := evEq.heap_extends
    have hxPm := Bytes.repAddressRef_heapMono₂ Core.addrTy extPm hxW
    have _ := projection_member_spec hC.runStore hC.hashedStored ⟨b_stop, hxPm, rfl⟩ evPm hsubPm
    have hxNb := Bytes.repAddressRef_heapMono₂ Core.addrTy evPm.heap_extends hxPm
    have hnb : Claim.NotBlockIn calls (Core.ixAddr b_stop) := by
      obtain ⟨rawNb, cNb, hhNb, hblNb, hdeNb, hnotM⟩ :=
        (Claim.assert_not_block_ref_notBlock ⟨b_stop, hxNb, rfl⟩ evNb).2
      exact ⟨rawNb, cNb, Core.hashed_mono hsubNb hhNb, hblNb, hdeNb, hnotM⟩
    have hxCi := Bytes.repAddressRef_heapMono₂ Core.addrTy evNb.heap_extends hxNb
    obtain ⟨raw, c, hsz, hhCi, hblCi, hdeECi, -, -⟩ := Claim.get_ci_head hxCi evCi
    have hrec : recordOf E₀ (Core.ixAddr b_stop) = some c := by
      rw [← hblCi]
      exact Claim.recordOf_hashed hC.runStore hC.hashedStored (Core.hashed_mono hsubCi hhCi)
        hsz (L1.deConstant_of_deConstantExact hdeECi) hdeECi
    have hprojFacts : IsProj c → usedRefIdxs c = [] ∧
        ∃ cb, recordOf E₀ (Ix.Cert.ownerOf (Core.ixAddr b_stop) c) = some cb ∧
          ConstAddrOf (Ix.Cert.ownerOf (Core.ixAddr b_stop) c) cb (Core.ixAddr b_stop) := by
      intro hpr
      exact ⟨proj_usedRefIdxs_nil hC.runStore hxCi evCi hsubCi hrec hpr,
        Claim.proj_member_of_load hC.runStore hC.hashedStored hxCi evCi hsubCi hrec hpr⟩
    have extTail := evEq.heap_extends.trans (evPm.heap_extends.trans
      (evNb.heap_extends.trans (evCi.heap_extends.trans evCov.heap_extends)))
    exact ⟨⟨bytes3, by rw [hr, hh]; exact L1.Stream.mono extTail hs3⟩,
      Or.inr (Or.inl ⟨hpos, hnb, c, hrec, hprojFacts⟩)⟩
  | .n2 (hv314 := hk2) (ev328 := evCnt) (cs_gfiphqsh := csW) (ev_dpuowbtw := evW)
      (cs412 := csCr) (ev414 := evCr) (ev_yqkzbtyw := evCov)
      (he440 := hr) (he441 := hh) (hc442 := hcs) .. =>
    obtain ⟨n, bytes2, -, hnEq, hs2, hm316⟩ := get_count_spec hs evCnt
    subst hnEq hm316
    have hsubW : ∀ cl ∈ csW, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsubCr : ∀ cl ∈ csCr, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    obtain ⟨b_ib, bytes3, hbIb, hs3, hpos⟩ :=
      walk_from_block_spec hC.runStore hC.hashedStored hblk hs2 evW hsubW
    have extW := evW.heap_extends
    have extTail := evCr.heap_extends.trans evCov.heap_extends
    exact ⟨⟨bytes3, by rw [hr, hh]; exact L1.Stream.mono extTail hs3⟩,
      Or.inr (Or.inr (Or.inl ⟨hk2, Core.ixAddr b_ib, hpos, _, _, _, _, _, _, csCr,
        hrc.mono extW,
        ⟨b_x, Bytes.repAddressRef_heapMono₂ Core.addrTy extW hx, rfl⟩,
        ⟨b_ib, hbIb, rfl⟩,
        evCr, hsubCr⟩))⟩
  | .n3 (x_iblock := x_iblock) (m570 := m570) (v684 := v684) (m685 := m685) (hv447 := hk3)
      (ev461 := evCnt) (cs_frlxnmjz := csW) (ev_ndaajwbz := evW)
      (ev547 := evIdx) (ev582 := evC1) (cs687 := csSg) (sg692 := sg)
      (ev717 := evEq) (heq740 := heq1) (cs_gufnlnhk := csCi) (ev_gwtfngxo := evCi)
      (ev_xxjagmga := evCov) (he742 := hr) (he743 := hh) (hc744 := hcs) .. =>
    obtain ⟨n, bytes2, -, hnEq, hs2, hm449⟩ := get_count_spec hs evCnt
    subst hnEq
    have hsubW : ∀ cl ∈ csW, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsubSg : ∀ cl ∈ csSg, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsubCi : ∀ cl ∈ csCi, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    obtain ⟨b_ib, bytes3, hbIb, hs3, hpos⟩ :=
      walk_from_block_spec hC.runStore hC.hashedStored (by rw [hm449]; exact hblk) hs2 evW hsubW
    obtain ⟨idx, bytes4, -, hidxEq, hs4, hm535⟩ := get_count_spec hs3 evIdx
    subst hidxEq
    obtain ⟨c1, bytes5, -, hc1Eq, hs5, hm570⟩ := get_count_spec hs4 evC1
    subst hc1Eq
    have hbIb570 : Bytes.RepAddressRef Core.addrTy m570 b_ib x_iblock := by
      rw [hm570, hm535]; exact hbIb
    have hprojHash : ∃ (a_out : Bytes.Address) (c_proj : Ixon.Constant),
        IsProj c_proj ∧ Ix.Cert.ownerOf (Core.ixAddr a_out) c_proj = Core.ixAddr b_ib ∧
        usedRefIdxs c_proj = [] ∧
        Bytes.RepAddressRef Core.addrTy m685 a_out v684 ∧
        Core.ixAddr a_out = Address.blake3Pure (Ixon.serConstant c_proj) ∧
        Hashed calls (Ixon.serConstant c_proj) ∧
        c_proj.wireWF ∧ Heap.Extends m570 m685 := by
      match sg with
      | .n0 (cs621 := csP) (ev623 := evP) (hc640 := hcsP) .. =>
        obtain ⟨a_out, c_proj, rfl, haOut, hixOut, hhashP, hwfP⟩ :=
          compute_iprj_addr_raw (t := t) hbIb570 evP
        have hsubP : ∀ cl ∈ csP, cl ∈ calls := fun cl hcl => hsubSg cl (by rw [hcsP]; simp [hcl])
        exact ⟨a_out, _, Or.inr (Or.inl ⟨_, rfl⟩), rfl, rfl, haOut, hixOut,
          Core.hashed_mono hsubP hhashP, hwfP, evP.heap_extends⟩
      | .other (cs648 := csP) (op674 := opSub) (ev650 := evP) (hc683 := hcsP) .. =>
        simp only [evalBinOp, Except.ok.injEq] at opSub
        subst opSub
        obtain ⟨a_out, c_proj, rfl, haOut, hixOut, hhashP, hwfP⟩ :=
          projection_addr_ctor_raw (t := t) hbIb570 evP
        have hsubP : ∀ cl ∈ csP, cl ∈ calls := fun cl hcl => hsubSg cl (by rw [hcsP]; simp [hcl])
        exact ⟨a_out, _, Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)), rfl, rfl, haOut, hixOut,
          Core.hashed_mono hsubP hhashP, hwfP, evP.heap_extends⟩
    obtain ⟨a_out, c_proj, hpr, hownEq, husedNil, haOut, hixOut, hhashP, hwfP, extSg⟩ := hprojHash
    have ext570 : Heap.Extends h m570 := by
      rw [hm570, hm535, ← hm449]; exact evW.heap_extends
    have hx685 := Bytes.repAddressRef_heapMono₂ Core.addrTy (ext570.trans extSg) hx
    obtain ⟨heqV, hmEq⟩ := Lib.address_eq_spec evEq haOut hx685
    have ea : a_out = b_x := by
      by_cases hne : a_out = b_x
      · exact hne
      · simp [hne] at heqV
        exact absurd (Value.field.inj (heqV.symm.trans heq1)) zero_ne_one
    subst ea
    have hxCi := Bytes.repAddressRef_heapMono₂ Core.addrTy evEq.heap_extends hx685
    obtain ⟨raw, c_ld, hsz, hhCi, hblCi, hdeECi, -, -⟩ := Claim.get_ci_head hxCi evCi
    have hrec_ld : recordOf E₀ (Core.ixAddr a_out) = some c_ld := by
      rw [← hblCi]
      exact Claim.recordOf_hashed hC.runStore hC.hashedStored (Core.hashed_mono hsubCi hhCi)
        hsz (L1.deConstant_of_deConstantExact hdeECi) hdeECi
    have eraw : raw = Ixon.serConstant c_proj :=
      hC.runStore.hashed_inj (Core.hashed_mono hsubCi hhCi) hhashP (hblCi.trans hixOut)
    have ec_eq : c_ld = c_proj := by
      rw [eraw, Ixon.Verify.deConstantExact_serConstant c_proj hwfP] at hdeECi
      exact (Except.ok.inj hdeECi).symm
    subst ec_eq
    obtain ⟨cib, hcib, hca⟩ :=
      Claim.proj_member_of_load hC.runStore hC.hashedStored hxCi evCi hsubCi hrec_ld hpr
    rw [hownEq] at hcib hca
    have extTail := extSg.trans (evEq.heap_extends.trans (evCi.heap_extends.trans evCov.heap_extends))
    exact ⟨⟨bytes5, by rw [hr, hh]; exact L1.Stream.mono extTail hs5⟩,
      Or.inr (Or.inr (Or.inr ⟨Core.ixAddr b_ib, c_ld, cib, hpos, hrec_ld, hpr, hownEq,
        husedNil, hcib, hca⟩))⟩

/-- **`KernelModeled::check_witnesses`**: extracts the witness list `outs`, proves `OpOrderedAt`
and `WitnessClassified` for every witness, ties kind-2 witnesses directly to `DirectContWitness`,
and preserves `L1.Stream`. -/
theorem check_witnesses_spec {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat}
    (hC : CollisionFreeRun calls E₀) :
    ∀ (k : Nat) {x_rc x_blk x_s x_out x_s' : SourceValue F} {nf : F}
      {b_blk : Bytes.Address} {bytes : List UInt8} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val nf = k →
      Claim.RCLimRep t bAddr lim h x_rc →
      Bytes.RepAddressRef Core.addrTy h b_blk x_blk →
      L1.Stream h bytes x_s →
      ObsFn Obs.W "KernelModeled::check_witnesses" [x_rc, x_blk, x_s, .field nf] h
        (.tuple [x_out, x_s']) h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∃ (outs : List Bytes.Address) (bytes' : List UInt8),
        RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h' outs x_out ∧
        L1.Stream h' bytes' x_s' ∧
        (∀ b ∈ outs, Claim.OpOrderedAt t lim (Core.ixAddr b)) ∧
        (∀ b ∈ outs, WitnessClassified calls bAddr t E₀ lim (Core.ixAddr b_blk) (Core.ixAddr b)) ∧
        (∀ b ∈ outs,
          (∃ ro : Ix.Kernel.Role, t.addressOf? ro = some (Core.ixAddr b) ∧
            Ix.SpecDigest.groupOf ro < 6 ∧
            (RoleVal.roleWalksBound ro = true ∨ RoleVal.isQuotRole ro = true)) ∨
          (PathPos E₀ (Core.ixAddr b_blk) (Core.ixAddr b) ∧ Claim.NotBlockIn calls (Core.ixAddr b) ∧
            ∃ c, recordOf E₀ (Core.ixAddr b) = some c ∧
              (IsProj c → usedRefIdxs c = [] ∧
                ∃ cb, recordOf E₀ (Ix.Cert.ownerOf (Core.ixAddr b) c) = some cb ∧
                  ConstAddrOf (Ix.Cert.ownerOf (Core.ixAddr b) c) cb (Core.ixAddr b))) ∨
          (DirectContWitness x_rc x_blk (Core.ixAddr b) x_s (.field nf) x_out x_s' h h' cs) ∨
          (∃ ib c cib, PathPos E₀ (Core.ixAddr b_blk) ib ∧
            recordOf E₀ (Core.ixAddr b) = some c ∧ IsProj c ∧
            Ix.Cert.ownerOf (Core.ixAddr b) c = ib ∧ usedRefIdxs c = [] ∧
            recordOf E₀ ib = some cib ∧ ConstAddrOf ib cib (Core.ixAddr b)))
  | 0, x_rc, x_blk, x_s, x_out, x_s', nf, b_blk, bytes, h, h', cs,
      hnf, hrc, hblk, hs, ev, _ => by
    have hnf0 : nf = 0 := by simpa [hnf] using (ZMod.natCast_zmod_val nf).symm
    subst hnf0
    match Obs.«KernelModeled::check_witnesses».obs ev with
    | .n0 (m21 := m21) (he19 := hr) (hm29 := hm) (he40 := hh) .. =>
      injection hr with hargs
      injection hargs with h1 h2
      injection h2 with h3 _
      subst h1 h3
      have ext : Heap.Extends h h' := by rw [hh, hm]; exact Heap.Extends.snoc _ _
      have cell : h'[h.length]? = some (.construct Core.addrListEnum "Nil" []) := by
        rw [hh, hm]; simp [Core.addrListEnum]
      exact ⟨[], bytes, RepLinkedList.nil cell, L1.Stream.mono ext hs,
        (fun _ hb => by cases hb), (fun _ hb => by cases hb), (fun _ hb => by cases hb)⟩
    | .other (hne42 := hne) .. => exact absurd rfl hne
  | k + 1, x_rc, x_blk, x_s, x_out, x_s', nf, b_blk, bytes, h, h', cs,
      hnf, hrc, hblk, hs, ev, hsub => by
    have hnfne : nf ≠ 0 := by intro h0; subst h0; simp at hnf
    match Obs.«KernelModeled::check_witnesses».obs ev with
    | .n0 (hv14 := hv) .. => exact absurd (Value.field.inj hv) hnfne
    | .other (m47 := m47) (cs57 := cs57) (x_x := x_x) (x_s2 := x_s2)
        (m82 := m82) (cs92 := cs92) (x_kind := x_kind) (x_s3 := x_s3)
        (m_phvyohte := m_ord) (cs_sjcjqvwo := cs_ord)
        (v116 := v_ns) (m117 := m117) (cs127 := cs127)
        (v133 := v_kf) (m157 := m157) (cs165 := cs165)
        (m184 := m184) (cs194 := cs194) (v200 := v200) (x_rest := x_rest) (x_s5 := x_s5')
        (m256 := m256) (hne42 := hne)
        (ev59 := evAddr) (ev94 := evByte) (ev_updedcyj := evOrd)
        (ev167 := evU8) (ev129 := evWit) (op235 := opSub) (ev196 := evRec)
        (he254 := hr) (hm264 := hm) (he291 := hh) (hc292 := hcs) .. =>
      injection hr with hargs
      injection hargs with h1 h2
      injection h2 with h3 _
      subst h1 h3
      obtain ⟨b_x, rem2, x_t, x_s2', -, htupA, hbX, hs2, extA, -⟩ :=
        Decl.get_address_spec hs evAddr
      injection htupA with haA
      injection haA with h1A h2A
      injection h2A with h3A _
      subst h1A h3A
      obtain ⟨hm82, bKind, rem3, _, hcons, hs3, htupB⟩ :=
        Deserialize.readByte_refines hs2 evByte.erase
      injection htupB with haB
      injection haB with h1B h2B
      injection h2B with h3B _
      subst h1B h3B
      have hrc82 : Claim.RCLimRep t bAddr lim m82 x_rc := hrc.mono (by rw [hm82]; exact extA)
      have hbx82 : Bytes.RepAddressRef Core.addrTy m82 b_x x_x := by rw [hm82]; exact hbX
      have hordX : Claim.OpOrderedAt t lim (Core.ixAddr b_x) :=
        assert_in_order_spec hrc82 ⟨b_x, hbx82, rfl⟩ evOrd
      obtain ⟨hvfEq, hm157⟩ := Lib.u8_to_field_spec evU8
      have extA82 : Heap.Extends h m82 := by rw [hm82]; exact extA
      have extOrd157 : Heap.Extends m82 m157 := by rw [hm157]; exact evOrd.heap_extends
      have ext157 : Heap.Extends h m157 := extA82.trans extOrd157
      have hsub127 : ∀ cl ∈ cs127, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hsub194 : ∀ cl ∈ cs194, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hbx157 := Bytes.repAddressRef_heapMono₂ Core.addrTy extOrd157 hbx82
      have hs3_82 : L1.Stream m82 rem3 x_s3 := by rw [hm82]; exact hs3
      obtain ⟨⟨bytes_ns, hs_ns⟩, hclsX⟩ :=
        check_witness_spec hC (hrc.mono ext157)
          (Bytes.repAddressRef_heapMono₂ Core.addrTy ext157 hblk)
          hbx157 (L1.Stream.mono extOrd157 hs3_82) evWit hsub127
      have ext117 : Heap.Extends h m117 := ext157.trans evWit.heap_extends
      simp only [evalBinOp, Except.ok.injEq] at opSub
      subst opSub
      have hvalSub : ZMod.val (nf - 1) = k := by
        rw [zmod_val_sub_one hnfne, hnf]; omega
      obtain ⟨rest, bytes', hrestRep, hs', hrestOrd, hrestCls, hrestDc⟩ :=
        check_witnesses_spec hC k hvalSub (hrc.mono ext117)
          (Bytes.repAddressRef_heapMono₂ Core.addrTy ext117 hblk) hs_ns evRec hsub194
      have extCons : Heap.Extends m184 h' := by rw [hh, hm]; exact Heap.Extends.snoc _ _
      have cell : h'[m184.length]? =
          some (.construct Core.addrListEnum "Cons" [x_x, x_rest]) := by
        rw [hh, hm]; simp [Core.addrListEnum]
      have hbxEnd := Bytes.repAddressRef_heapMono₂ Core.addrTy
        (evWit.heap_extends.trans (evRec.heap_extends.trans extCons)) hbx157
      have hlistRep : RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h'
          (b_x :: rest) (.ptr (.enum Core.addrListEnum) m184.length) :=
        RepLinkedList.cons cell hbxEnd
          (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) extCons hrestRep)
      refine ⟨b_x :: rest, bytes', hlistRep, L1.Stream.mono extCons hs', ?_, ?_, ?_⟩
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact hordX
        · exact hrestOrd b hb'
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · rcases hclsX with h0 | h1 | ⟨-, h2⟩ | h3
          · exact Or.inl h0
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr (Or.inl h2))
          · exact Or.inr (Or.inr (Or.inr h3))
        · exact hrestCls b hb'
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · rcases hclsX with h0 | h1 | ⟨hk2, -⟩ | h3
          · exact Or.inl h0
          · exact Or.inr (Or.inl h1)
          · subst hk2
            exact Or.inr (Or.inr (Or.inl (DirectContWitness.head hne evAddr evByte evOrd evU8
              evWit rfl evRec ⟨b, hbx157, rfl⟩ rfl hm hh hcs)))
          · exact Or.inr (Or.inr (Or.inr h3))
        · rcases hrestDc b hb' with h0 | h1 | h2 | h3
          · exact Or.inl h0
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr (Or.inl (DirectContWitness.tail hne evAddr evByte evOrd evU8
              evWit rfl evRec h2 rfl hm hh hcs)))
          · exact Or.inr (Or.inr (Or.inr h3))

/-- Two represented address lists at the same heap and pointer are equal. -/
theorem addrList_rep_det {h : Heap F} :
    ∀ {xs ys : List Bytes.Address} {p : SourceValue F},
      RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h xs p →
      RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h ys p →
      xs = ys
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, .nil c1, .cons c2 _ _ => by rw [c1] at c2; simp at c2
  | _ :: _, [], _, .cons c1 _ _, .nil c2 => by rw [c1] at c2; simp at c2
  | x :: xs, y :: ys, _, .cons c1 hx hxs, .cons c2 hy hys => by
    rw [c1] at c2
    injection c2 with hc
    injection hc with _ _ hargs
    simp only [List.cons.injEq] at hargs
    obtain ⟨hpx, hpr, -⟩ := hargs
    subst hpx hpr
    have exy : x = y := Bytes.repAddressRef_inj U32.Goldilocks.compatible hx hy
    subst exy
    exact congrArg (x :: ·) (addrList_rep_det hxs hys)

/-- **Extracting facts from `DirectContWitness`**: a directly witnessed container recursor `x`
is in the witness list `outs`, is `OpOrderedAt`, has `ContainerRecIn cs x`, and was checked by
`check_container_rec(rc, x, ib)` for some `ib` with `PathPos E₀ B ib`. -/
theorem DirectContWitness.extract {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat}
    (hC : CollisionFreeRun calls E₀)
    {x_rc x_blk : SourceValue F} {x : _root_.Address}
    {x_s x_n x_out x_s' : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hdw : DirectContWitness x_rc x_blk x x_s x_n x_out x_s' h h' cs) :
    ∀ {b_blk : Bytes.Address} {bytes : List UInt8},
      Claim.RCLimRep t bAddr lim h x_rc →
      Bytes.RepAddressRef Core.addrTy h b_blk x_blk →
      L1.Stream h bytes x_s →
      (∀ cl ∈ cs, cl ∈ calls) →
      (∃ outs, RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h' outs x_out ∧
          x ∈ outs.map Core.ixAddr) ∧
        Claim.OpOrderedAt t lim x ∧
        ContainerRecIn cs x ∧
        ∃ ib, PathPos E₀ (Core.ixAddr b_blk) ib ∧
          ∃ (h₁ h₂ : Heap F) (rc₁ xx₁ xib₁ r₁ : SourceValue F) (cs₁ : List (Call F)),
            Claim.RCLimRep t bAddr lim h₁ rc₁ ∧
            Core.S0.addr h₁ xx₁ x ∧ Core.S0.addr h₁ xib₁ ib ∧
            ObsFn Obs.W "KernelModeled::check_container_rec" [rc₁, xx₁, xib₁] h₁ r₁ h₂ cs₁ ∧
            (∀ cl ∈ cs₁, cl ∈ calls) := by
  induction hdw with
  | @head x_s x_n x_out x_s' h h' cs m47 m82 m_ord m157 m117 m184 m256
      x_x x_s2 x_kind x_s3 v_ord v_ns x_rest v200 cs57 cs92 cs_ord cs165 cs127 cs194
      hne evAddr evByte evOrd evU8 evWit opSub evRec hx hr hm hh hcs =>
    intro b_blk bytes hrc hblk hs hsub
    obtain ⟨b_x, rem2, x_t, x_s2', -, htupA, hbX, hs2, extA, -⟩ :=
      Decl.get_address_spec hs evAddr
    injection htupA with haA
    injection haA with h1A h2A
    injection h2A with h3A _
    subst h1A h3A
    obtain ⟨hm82, bKind, rem3, _, -, hs3, htupB⟩ :=
      Deserialize.readByte_refines hs2 evByte.erase
    injection htupB with haB
    injection haB with h1B h2B
    injection h2B with h3B _
    subst h1B h3B
    have hrc82 : Claim.RCLimRep t bAddr lim m82 x_rc := hrc.mono (by rw [hm82]; exact extA)
    have hbx82 : Bytes.RepAddressRef Core.addrTy m82 b_x x_x := by rw [hm82]; exact hbX
    have hordX : Claim.OpOrderedAt t lim (Core.ixAddr b_x) :=
      assert_in_order_spec hrc82 ⟨b_x, hbx82, rfl⟩ evOrd
    obtain ⟨-, hm157⟩ := Lib.u8_to_field_spec evU8
    have extA82 : Heap.Extends h m82 := by rw [hm82]; exact extA
    have ext82_157 : Heap.Extends m82 m157 := by rw [hm157]; exact evOrd.heap_extends
    have ext157 : Heap.Extends h m157 := extA82.trans ext82_157
    have hbx157 := Bytes.repAddressRef_heapMono₂ Core.addrTy ext82_157 hbx82
    have hs3_82 : L1.Stream m82 rem3 x_s3 := by rw [hm82]; exact hs3
    obtain ⟨b_x', hbX', hixEq⟩ := hx
    have ebEq : b_x = b_x' := Bytes.repAddressRef_inj U32.Goldilocks.compatible hbx157 hbX'
    subst ebEq
    have hxEq : x = Core.ixAddr b_x := hixEq.symm
    subst hxEq
    have hsub127 : ∀ cl ∈ cs127, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsub194 : ∀ cl ∈ cs194, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    -- Unfold `evWit` directly at kind 2 to get `ContainerRecIn cs` and `check_container_rec`
    match Obs.«KernelModeled::check_witness».obs evWit with
    | .n0 (hv14 := h0) .. => exact absurd (Value.field.inj h0) (by decide)
    | .n1 (hv171 := h1) .. => exact absurd (Value.field.inj h1) (by decide)
    | .n3 (hv447 := h3) .. => exact absurd (Value.field.inj h3) (by decide)
    | .n2 (m_gmdkwlsb := mCr) (x_iblock := x_iblock) (ev328 := evCnt) (cs_gfiphqsh := csW)
        (ev_dpuowbtw := evW) (cs412 := csCr) (ev414 := evCr) (ev_yqkzbtyw := evCov)
        (he440 := hrW) (he441 := hhW) (hc442 := hcsW) .. =>
      obtain ⟨_, bytes2, -, hnEq, hs2', hm316⟩ :=
        get_count_spec (L1.Stream.mono ext82_157 hs3_82) evCnt
      subst hnEq hm316
      have hsubW : ∀ cl ∈ csW, cl ∈ calls := fun cl hcl => hsub127 cl (by rw [hcsW]; simp [hcl])
      have hsubCr : ∀ cl ∈ csCr, cl ∈ calls := fun cl hcl => hsub127 cl (by rw [hcsW]; simp [hcl])
      obtain ⟨b_ib, bytes3, hbIb, hs3', hpos⟩ :=
        walk_from_block_spec hC.runStore hC.hashedStored
          (Bytes.repAddressRef_heapMono₂ Core.addrTy ext157 hblk)
          hs2' evW hsubW
      have extW := evW.heap_extends
      have hcrCall : ContainerRecIn cs (Core.ixAddr b_x) := by
        refine ⟨x_rc, x_x, x_iblock, mCr, ?_,
          ⟨b_x, Bytes.repAddressRef_heapMono₂ Core.addrTy extW hbx157, rfl⟩⟩
        rw [hcs, hcsW]
        simp
      have hs_ns : L1.Stream m117 bytes3 v_ns := by
        rw [hrW, hhW]
        exact L1.Stream.mono (evCr.heap_extends.trans evCov.heap_extends) hs3'
      have ext117 : Heap.Extends h m117 := ext157.trans evWit.heap_extends
      -- Extract `outs` from `evRec` via `check_witnesses_spec`
      have hv200f : ∃ nf : F, v200 = .field nf := by
        cases x_n <;> simp [evalBinOp] at opSub
        exact ⟨_, opSub.symm⟩
      obtain ⟨nf2, rfl⟩ := hv200f
      obtain ⟨rest, -, hrestRep, -, -, -, -⟩ :=
        check_witnesses_spec hC (ZMod.val nf2) rfl (hrc.mono ext117)
          (Bytes.repAddressRef_heapMono₂ Core.addrTy ext117 hblk) hs_ns evRec hsub194
      have extCons : Heap.Extends m184 h' := by rw [hh, hm]; exact Heap.Extends.snoc _ _
      have cell : h'[m184.length]? =
          some (.construct Core.addrListEnum "Cons" [x_x, x_rest]) := by
        rw [hh, hm]; simp [Core.addrListEnum]
      have hbxEnd := Bytes.repAddressRef_heapMono₂ Core.addrTy
        (evWit.heap_extends.trans (evRec.heap_extends.trans extCons)) hbx157
      have houts : RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h'
          (b_x :: rest) x_out := by
        rw [hr]
        exact RepLinkedList.cons cell hbxEnd
          (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) extCons hrestRep)
      exact ⟨⟨b_x :: rest, houts, by simp⟩, hordX, hcrCall,
        Core.ixAddr b_ib, hpos, _, _, _, _, _, _, csCr,
        hrc.mono (ext157.trans extW),
        ⟨b_x, Bytes.repAddressRef_heapMono₂ Core.addrTy extW hbx157, rfl⟩,
        ⟨b_ib, hbIb, rfl⟩,
        evCr, hsubCr⟩
  | @tail x_s x_n x_out x_s' h h' cs m47 m82 m_ord m157 m117 m184 m256
      x_x x_s2 x_kind x_s3 v_ord v_kf v_ns x_rest v200 cs57 cs92 cs_ord cs165 cs127 cs194
      hne evAddr evByte evOrd evU8 evWit opSub evRec htail hr hm hh hcs ih =>
    intro b_blk bytes hrc hblk hs hsub
    obtain ⟨b_x, rem2, x_t, x_s2', -, htupA, hbX, hs2, extA, -⟩ :=
      Decl.get_address_spec hs evAddr
    injection htupA with haA
    injection haA with h1A h2A
    injection h2A with h3A _
    subst h1A h3A
    obtain ⟨hm82, bKind, rem3, _, -, hs3, htupB⟩ :=
      Deserialize.readByte_refines hs2 evByte.erase
    injection htupB with haB
    injection haB with h1B h2B
    injection h2B with h3B _
    subst h1B h3B
    obtain ⟨-, hm157⟩ := Lib.u8_to_field_spec evU8
    have extA82 : Heap.Extends h m82 := by rw [hm82]; exact extA
    have ext82_157 : Heap.Extends m82 m157 := by rw [hm157]; exact evOrd.heap_extends
    have ext157 : Heap.Extends h m157 := extA82.trans ext82_157
    have hbx157 := Bytes.repAddressRef_heapMono₂ Core.addrTy ext82_157 (by rw [hm82]; exact hbX)
    have hs3_82 : L1.Stream m82 rem3 x_s3 := by rw [hm82]; exact hs3
    have hsub127 : ∀ cl ∈ cs127, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsub194 : ∀ cl ∈ cs194, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    obtain ⟨⟨bytes_ns, hs_ns⟩, -⟩ :=
      check_witness_spec hC (hrc.mono ext157)
        (Bytes.repAddressRef_heapMono₂ Core.addrTy ext157 hblk)
        hbx157 (L1.Stream.mono ext82_157 hs3_82) evWit hsub127
    have ext117 : Heap.Extends h m117 := ext157.trans evWit.heap_extends
    obtain ⟨⟨rest, hrestRep, hxMem⟩, hordX, hcrRest, hcrWit⟩ :=
      ih (hrc.mono ext117) (Bytes.repAddressRef_heapMono₂ Core.addrTy ext117 hblk) hs_ns hsub194
    have extCons : Heap.Extends m184 h' := by rw [hh, hm]; exact Heap.Extends.snoc _ _
    have cell : h'[m184.length]? =
        some (.construct Core.addrListEnum "Cons" [x_x, x_rest]) := by
      rw [hh, hm]; simp [Core.addrListEnum]
    have hbxEnd := Bytes.repAddressRef_heapMono₂ Core.addrTy
      (evWit.heap_extends.trans (evRec.heap_extends.trans extCons)) hbx157
    have houts : RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h'
        (b_x :: rest) x_out := by
      rw [hr]
      exact RepLinkedList.cons cell hbxEnd
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) extCons hrestRep)
    refine ⟨⟨b_x :: rest, houts, List.mem_cons_of_mem _ hxMem⟩, hordX, ?_, hcrWit⟩
    obtain ⟨rc₁, xa₁, ib₁, h₁, hmem₁, hxa₁⟩ := hcrRest
    exact ⟨rc₁, xa₁, ib₁, h₁, by rw [hcs]; simp [hmem₁], hxa₁⟩

/-- **Every address listed in a family check's own advice list has an `AdviceIn cs` call.** -/
theorem adviceListedIn_toAdviceIn {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} {advAs : List Bytes.Address} {a : _root_.Address}
    (hown : FamilyCallOwn calls bAddr t B rb lim cs advAs) (ha : AdviceListedIn advAs a) :
    AdviceIn cs a := by
  obtain ⟨h, h', rc, xb, xrb, r, -, -, -, -, w, -, -⟩ := hown
  obtain ⟨m, m', xadv, wset, v, cs_adv, -, hadv, ev_adv, hsub_adv⟩ := w.walk_nil
  obtain ⟨b, hb, rfl⟩ := ha
  obtain ⟨-, hadvIn, -⟩ :=
    Decl.check_advice_records_walk advAs (fun _ => False) hadv .nil ev_adv
  obtain ⟨rc₁, xa, aset, wset₁, m₁, hmemCall, hxa⟩ := hadvIn b hb
  exact ⟨rc₁, xa, aset, wset₁, m₁, hsub_adv _ hmemCall, hxa⟩

private theorem directContWitness_toContainerRecIn {rc xb : SourceValue F} {x : _root_.Address}
    {x_s x_n x_out x_s' : SourceValue F} {h h' : Heap F} {cs_ws : List (Call F)}
    (hdw : DirectContWitness rc xb x x_s x_n x_out x_s' h h' cs_ws) :
    ContainerRecIn cs_ws x := by
  induction hdw with
  | head _ _ _ _ _ evWit _ _ hx _ _ _ hcs =>
    match Obs.«KernelModeled::check_witness».obs evWit with
    | .n0 (hv14 := h0) .. => exact absurd (Value.field.inj h0) (by decide)
    | .n1 (hv171 := h1) .. => exact absurd (Value.field.inj h1) (by decide)
    | .n3 (hv447 := h3) .. => exact absurd (Value.field.inj h3) (by decide)
    | .n2 (m_gmdkwlsb := mCr) (x_iblock := x_iblock) (ev328 := evCnt) (ev_dpuowbtw := evW)
        (hc442 := hcsW) .. =>
      refine ⟨rc, _, x_iblock, mCr, ?_,
        Core.S0.addr_mono (evCnt.heap_extends.trans evW.heap_extends) hx⟩
      rw [hcs, hcsW]; simp
  | tail _ _ _ _ _ _ _ _ _ _ _ _ hcs ih =>
    obtain ⟨rc₁, xa₁, ib₁, h₁, hmem₁, hxa₁⟩ := ih
    exact ⟨rc₁, xa₁, ib₁, h₁, by rw [hcs]; simp [hmem₁], hxa₁⟩

/-- **Every directly witnessed container recursor of a family check has `ContainerRecIn cs x`.** -/
theorem directContOwn_toContainerRecIn {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} {advAs : List Bytes.Address} {x : _root_.Address}
    (hdc : DirectContOwn calls bAddr t B rb lim cs advAs x) :
    ContainerRecIn cs x := by
  obtain ⟨h, h', rc, xb, xrb, r, _, _, _, _, g, _, _⟩ := hdc
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, cs_ws, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    sub_ws, _, _, _, _, hcont⟩ := g
  obtain ⟨rc₁, xa₁, ib₁, h₁, hmem₁, hxa₁⟩ := directContWitness_toContainerRecIn (hcont x rfl)
  exact ⟨rc₁, xa₁, ib₁, h₁, sub_ws _ hmem₁, hxa₁⟩

/-! ## Reference-guard helpers -/

/-- **`KernelModeled::used_ref_has`**: returning `1` witnesses `UsedRef E₀ ib r`. -/
theorem used_ref_has_spec {E₀ : Ixon.Env} {ib r : _root_.Address} {c_ib : Ixon.Constant}
    (hcib : recordOf E₀ ib = some c_ib) (hsmall : c_ib.refs.size < 8589934592) :
    ∀ (xs : List _root_.Address) (i : Nat) {x_irefs x_iused x_r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      c_ib.refs.toList.drop i = xs →
      RepList Core.addrListEnum Claim.RepAddrElem h xs x_irefs →
      RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h (Core.S0.usedRefIdxs c_ib) x_iused →
      Core.S0.addr h x_r r →
      ObsFn Obs.W "KernelModeled::used_ref_has" [x_irefs, x_iused, .field (i : F), x_r]
        h (.field 1) h' cs →
      UsedRef E₀ ib r
  | [], i, x_irefs, x_iused, x_r, h, h', cs, _, hrefs, _, _, ev => by
    match Obs.«KernelModeled::used_ref_has».obs ev with
    | .Nil (he20 := h0) .. => exact absurd (Value.field.inj h0) one_ne_zero
    | .Cons_n1 (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hrefs ld
      cases he
  | q :: rest, i, x_irefs, x_iused, x_r, h, h', cs, hdrop, hrefs, hused, hr, ev => by
    have hiLt : i < c_ib.refs.size := by
      have hne : c_ib.refs.toList.drop i ≠ [] := by rw [hdrop]; simp
      have : i < c_ib.refs.toList.length := by
        by_contra hge
        exact hne (List.drop_eq_nil_iff.mpr (by omega))
      simpa using this
    have hiBound : i < 72057594037927936 := by omega
    match Obs.«KernelModeled::used_ref_has».obs ev with
    | .Nil (ld12 := ld) .. => exact absurd (Lib.rep_nil_of_load hrefs ld) (by simp)
    | .Cons_n1 (ld12 := ld) (sg113 := sg) .. =>
      obtain ⟨q', rest', he, ⟨bq, hbq, hqEq⟩, -⟩ := Lib.rep_cons_of_load hrefs ld
      injection he with hq' _
      subst hq'
      match sg with
      | .n1 (ev54 := evHas) (ev80 := evEq) .. =>
        obtain ⟨hmHas, hiff⟩ :=
          Claim.g_list_has_spec (Core.S0.usedRefIdxs c_ib) hiBound hused evHas
        have hmemUsed : i ∈ usedRefIdxs c_ib := by
          rw [← Assembly.usedRefIdxs_eq]; exact hiff.mp rfl
        obtain ⟨br, hbr, hrEq⟩ := hr
        obtain ⟨heqV, -⟩ := Lib.address_eq_spec evEq (by rw [hmHas]; exact hbq)
          (by rw [hmHas]; exact hbr)
        have eb : bq = br := by
          by_cases hne : bq = br
          · exact hne
          · simp [hne] at heqV
        subst eb
        have hqr : q = r := hqEq.symm.trans hrEq
        subst hqr
        have hget : c_ib.refs[i]? = some q := by
          rw [← Array.getElem?_toList, ← List.head?_drop, hdrop]
          rfl
        exact ⟨c_ib, i, hcib, hmemUsed, hget⟩
      | .other (he102 := h0) .. => exact absurd (Value.field.inj h0) one_ne_zero
    | .Cons_other (m106 := m106) (ld12 := ld) (sg113 := sg) (op172 := opAdd) (ev140 := evRec) .. =>
      obtain ⟨q', rest', he, -, hrest⟩ := Lib.rep_cons_of_load hrefs ld
      injection he with _ hrest'
      subst hrest'
      have extSg : Heap.Extends h m106 := by
        match sg with
        | .n1 (ev54 := e1) (ev80 := e2) .. => exact e1.heap_extends.trans e2.heap_extends
        | .other (ev54 := e1) (he103 := hh) .. => rw [hh]; exact e1.heap_extends
      simp only [evalBinOp, Except.ok.injEq] at opAdd
      subst opAdd
      have hcast : ((i : F) + 1) = ((i + 1 : Nat) : F) := by push_cast; rfl
      rw [hcast] at evRec
      have hdrop1 : c_ib.refs.toList.drop (i + 1) = rest := by
        have h1 : (c_ib.refs.toList.drop i).tail = c_ib.refs.toList.drop (i + 1) := by
          rw [List.tail_drop]
        rw [← h1, hdrop]; rfl
      exact used_ref_has_spec hcib hsmall rest (i + 1) hdrop1
        (RepLinkedList.mono Claim.repAddrElem_heapMono₂ extSg hrest)
        (RepLinkedList.mono (fun _ _ _ _ _ r => r) extSg hused)
        (Core.S0.addr_mono extSg hr) evRec

/-- **`KernelModeled::is_projection_of`**: returning `1` witnesses that `r` is a projection of
`blk` with no used references and `ConstAddrOf blk cb r`. -/
theorem is_projection_of_spec {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {r blk : _root_.Address} {x_r x_blk : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hr : Core.S0.addr h x_r r) (hblk : Core.S0.addr h x_blk blk)
    (ev : ObsFn Obs.W "KernelModeled::is_projection_of" [x_r, x_blk] h (.field 1) h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∃ c cb, recordOf E₀ r = some c ∧ IsProj c ∧ Ix.Cert.ownerOf r c = blk ∧
      usedRefIdxs c = [] ∧ recordOf E₀ blk = some cb ∧ ConstAddrOf blk cb r := by
  obtain ⟨br, hbr, rfl⟩ := hr
  obtain ⟨bblk, hbblk, rfl⟩ := hblk
  have hcase : ∀ {m2 m_ci m_pb : Heap F} {v_ci v_pb : SourceValue F}
      {cs12 cs_ci cs_pb cs_eq : List (Call F)} {vC : SourceValue F},
      ObsFn Obs.W "Ingress::load_verified_constant" [x_r] h vC m2 cs12 →
      ObsFn Obs.W "Ingress::get_ci" [x_r] m2 v_ci m_ci cs_ci →
      ObsFn Obs.W "KernelModeled::projection_block" [vC] m_ci v_pb m_pb cs_pb →
      ObsFn Obs.W "Bytes::address_eq" [v_pb, x_blk] m_pb (.field 1) h' cs_eq →
      (∀ cl ∈ cs12, cl ∈ calls) → (∀ cl ∈ cs_ci, cl ∈ calls) →
      ∃ c cb, recordOf E₀ (Core.ixAddr br) = some c ∧ IsProj c ∧
        Ix.Cert.ownerOf (Core.ixAddr br) c = Core.ixAddr bblk ∧
        usedRefIdxs c = [] ∧ recordOf E₀ (Core.ixAddr bblk) = some cb ∧
        ConstAddrOf (Core.ixAddr bblk) cb (Core.ixAddr br) := by
    intro m2 m_ci m_pb v_ci v_pb cs12 cs_ci cs_pb cs_eq vC evLd evCi evPb evEq hsub12 hsubCi
    obtain ⟨extLd, raw, c, hsz, hh, hbl, hde, hdeE, hrepC, -⟩ :=
      Claim.load_verified_constant_de ⟨br, hbr, rfl⟩ evLd
    have hrec : recordOf E₀ (Core.ixAddr br) = some c := by
      rw [← hbl]
      exact Claim.recordOf_hashed hS hH (Core.hashed_mono hsub12 hh) hsz hde hdeE
    have hbrCi := Bytes.repAddressRef_heapMono₂ Core.addrTy extLd hbr
    obtain ⟨-, hpr, b_own, hownRep, hownEq⟩ :=
      projection_block_claim_spec (a := Core.ixAddr br) (Claim.RepConstant.mono evCi.heap_extends hrepC) evPb
    have hbblkPb := Bytes.repAddressRef_heapMono₂ Core.addrTy
      (extLd.trans (evCi.heap_extends.trans evPb.heap_extends)) hbblk
    obtain ⟨heqV, -⟩ := Lib.address_eq_spec evEq hownRep hbblkPb
    have eb : b_own = bblk := by
      by_cases hne : b_own = bblk
      · exact hne
      · simp [hne] at heqV
    subst eb
    have husedNil := proj_usedRefIdxs_nil hS hbrCi evCi hsubCi hrec hpr
    obtain ⟨cb, hcb, hca⟩ := Claim.proj_member_of_load hS hH hbrCi evCi hsubCi hrec hpr
    rw [← hownEq] at hcb hca
    exact ⟨c, cb, hrec, hpr, hownEq.symm, husedNil, hcb, hca⟩
  match Obs.«KernelModeled::is_projection_of».obs ev with
  | .IPrj (cs12 := cs12) (cs_skilefqi := csCi) (ev14 := evLd) (ev_pvplyepc := evCi)
      (ev109 := evPb) (ev95 := evEq) (hc125 := hcs) .. =>
    exact hcase evLd evCi evPb evEq
      (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
      (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
  | .CPrj (cs12 := cs12) (cs_tafpebbo := csCi) (ev14 := evLd) (ev_rnaxgwez := evCi)
      (ev158 := evPb) (ev144 := evEq) (hc174 := hcs) .. =>
    exact hcase evLd evCi evPb evEq
      (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
      (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
  | .RPrj (cs12 := cs12) (cs_nwqbwyif := csCi) (ev14 := evLd) (ev_jqzwxbpt := evCi)
      (ev207 := evPb) (ev193 := evEq) (hc223 := hcs) .. =>
    exact hcase evLd evCi evPb evEq
      (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
      (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
  | .other (he228 := h0) .. => exact absurd (Value.field.inj h0) one_ne_zero

/-- **`KernelModeled::ref_projects_from`**: returning `1` witnesses a 2-step `PathPos E₀ ib blk`
(a used reference `q` of `ib` that projects from `blk`). -/
theorem ref_projects_from_spec {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {ib blk : _root_.Address} {c_ib : Ixon.Constant}
    (hcib : recordOf E₀ ib = some c_ib) (hsmall : c_ib.refs.size < 8589934592) :
    ∀ (xs : List _root_.Address) (i : Nat) {x_rc x_r x_irefs x_iused x_blk : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      c_ib.refs.toList.drop i = xs →
      RepList Core.addrListEnum Claim.RepAddrElem h xs x_irefs →
      RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h (Core.S0.usedRefIdxs c_ib) x_iused →
      Core.S0.addr h x_blk blk →
      ObsFn Obs.W "KernelModeled::ref_projects_from"
        [x_rc, x_r, x_irefs, x_iused, .field (i : F), x_blk] h (.field 1) h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      PathPos E₀ ib blk
  | [], i, x_rc, x_r, x_irefs, x_iused, x_blk, h, h', cs, _, hrefs, _, _, ev, _ => by
    match Obs.«KernelModeled::ref_projects_from».obs ev with
    | .Nil (he20 := h0) .. => exact absurd (Value.field.inj h0) one_ne_zero
    | .Cons_n1 (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hrefs ld
      cases he
  | q :: rest, i, x_rc, x_r, x_irefs, x_iused, x_blk, h, h', cs,
      hdrop, hrefs, hused, hblk, ev, hsub => by
    have hiLt : i < c_ib.refs.size := by
      have hne : c_ib.refs.toList.drop i ≠ [] := by rw [hdrop]; simp
      have : i < c_ib.refs.toList.length := by
        by_contra hge
        exact hne (List.drop_eq_nil_iff.mpr (by omega))
      simpa using this
    have hiBound : i < 72057594037927936 := by omega
    match Obs.«KernelModeled::ref_projects_from».obs ev with
    | .Nil (ld12 := ld) .. => exact absurd (Lib.rep_nil_of_load hrefs ld) (by simp)
    | .Cons_n1 (ld12 := ld) (sg113 := sg) (hc130 := hcs) .. =>
      obtain ⟨q', rest', he, hqAddr, -⟩ := Lib.rep_cons_of_load hrefs ld
      injection he with hq' _
      subst hq'
      match sg with
      | .n1_n1 (cs_mxfetwtb := csPr) (ev54 := evHas) (ev_crsszbsn := evPr)
          (hc_rfthzkdb := hcsSg) .. =>
        obtain ⟨hmHas, hiff⟩ :=
          Claim.g_list_has_spec (Core.S0.usedRefIdxs c_ib) hiBound hused evHas
        have hmemUsed : i ∈ usedRefIdxs c_ib := by
          rw [← Assembly.usedRefIdxs_eq]; exact hiff.mp rfl
        have hget : c_ib.refs[i]? = some q := by
          rw [← Array.getElem?_toList, ← List.head?_drop, hdrop]; rfl
        have hu : UsedRef E₀ ib q := ⟨c_ib, i, hcib, hmemUsed, hget⟩
        have hsubPr : ∀ cl ∈ csPr, cl ∈ calls := fun cl hcl =>
          hsub cl (by rw [hcs, hcsSg]; simp [hcl])
        obtain ⟨cq, _, hcq, hpr, hownEq, -, -, -⟩ :=
          is_projection_of_spec hS hH (by rw [hmHas]; exact hqAddr)
            (by rw [hmHas]; exact hblk) evPr hsubPr
        exact ⟨q, Or.inl hu, PathReach.single (Or.inr ⟨cq, hcq, hpr, hownEq.symm⟩)⟩
      | .n1_other (he_wiyazqbs := h0) .. => exact absurd (Value.field.inj h0) one_ne_zero
      | .other (he102 := h0) .. => exact absurd (Value.field.inj h0) one_ne_zero
    | .Cons_other (m106 := m106) (ld12 := ld) (cs138 := csRec) (sg113 := sg) (op_ifhibjja := opAdd)
        (ev140 := evRec) (hc181 := hcs) .. =>
      obtain ⟨q', rest', he, -, hrest⟩ := Lib.rep_cons_of_load hrefs ld
      injection he with _ hrest'
      subst hrest'
      have extSg : Heap.Extends h m106 := by
        match sg with
        | .n1_n1 (ev54 := e1) (ev_crsszbsn := e2) (ev_etesurje := e3) (ev_syhqofqg := e4) .. =>
          exact e1.heap_extends.trans (e2.heap_extends.trans (e3.heap_extends.trans e4.heap_extends))
        | .n1_other (ev54 := e1) (ev_crsszbsn := e2) (he_rviofgqu := hh) .. =>
          rw [hh]; exact e1.heap_extends.trans e2.heap_extends
        | .other (ev54 := e1) (he103 := hh) .. => rw [hh]; exact e1.heap_extends
      simp only [evalBinOp, Except.ok.injEq] at opAdd
      subst opAdd
      have hcast : ((i : F) + 1) = ((i + 1 : Nat) : F) := by push_cast; rfl
      rw [hcast] at evRec
      have hdrop1 : c_ib.refs.toList.drop (i + 1) = rest := by
        have h1 : (c_ib.refs.toList.drop i).tail = c_ib.refs.toList.drop (i + 1) := by
          rw [List.tail_drop]
        rw [← h1, hdrop]; rfl
      have hsubRec : ∀ cl ∈ csRec, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      exact ref_projects_from_spec hS hH hcib hsmall rest (i + 1) hdrop1
        (RepLinkedList.mono Claim.repAddrElem_heapMono₂ extSg hrest)
        (RepLinkedList.mono (fun _ _ _ _ _ r => r) extSg hused)
        (Core.S0.addr_mono extSg hblk) evRec hsubRec

/-- **`KernelModeled::projection_of_ref_block`**: returning `1` witnesses that `r` is an
`IPrj`/`CPrj` of some `blk` with `PathPos E₀ ib blk`, `usedRefIdxs = []`, and `ConstAddrOf`. -/
theorem projection_of_ref_block_spec {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {ib r : _root_.Address} {c_ib : Ixon.Constant}
    (hcib : recordOf E₀ ib = some c_ib) (hsmall : c_ib.refs.size < 8589934592)
    {x_rc x_r x_irefs x_iused : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hr : Core.S0.addr h x_r r)
    (hrefs : RepList Core.addrListEnum Claim.RepAddrElem h c_ib.refs.toList x_irefs)
    (hused : RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h
      (Core.S0.usedRefIdxs c_ib) x_iused)
    (ev : ObsFn Obs.W "KernelModeled::projection_of_ref_block" [x_rc, x_r, x_irefs, x_iused]
      h (.field 1) h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∃ blk c cb, PathPos E₀ ib blk ∧ recordOf E₀ r = some c ∧ IsProj c ∧
      Ix.Cert.ownerOf r c = blk ∧ usedRefIdxs c = [] ∧
      recordOf E₀ blk = some cb ∧ ConstAddrOf blk cb r := by
  obtain ⟨br, hbr, rfl⟩ := hr
  have hcase : ∀ {m2 m_ci m_pb : Heap F} {v_ci v_pb : SourceValue F}
      {cs12 cs_ci cs_pb cs_rpf : List (Call F)} {vC : SourceValue F},
      ObsFn Obs.W "Ingress::load_verified_constant" [x_r] h vC m2 cs12 →
      ObsFn Obs.W "Ingress::get_ci" [x_r] m2 v_ci m_ci cs_ci →
      ObsFn Obs.W "KernelModeled::projection_block" [vC] m_ci v_pb m_pb cs_pb →
      ObsFn Obs.W "KernelModeled::ref_projects_from"
        [x_rc, x_r, x_irefs, x_iused, .field 0, v_pb] m_pb (.field 1) h' cs_rpf →
      (∀ cl ∈ cs12, cl ∈ calls) → (∀ cl ∈ cs_ci, cl ∈ calls) → (∀ cl ∈ cs_rpf, cl ∈ calls) →
      ∃ blk c cb, PathPos E₀ ib blk ∧ recordOf E₀ (Core.ixAddr br) = some c ∧ IsProj c ∧
        Ix.Cert.ownerOf (Core.ixAddr br) c = blk ∧ usedRefIdxs c = [] ∧
        recordOf E₀ blk = some cb ∧ ConstAddrOf blk cb (Core.ixAddr br) := by
    intro m2 m_ci m_pb v_ci v_pb cs12 cs_ci cs_pb cs_rpf vC evLd evCi evPb evRpf hsub12 hsubCi hsubRpf
    obtain ⟨extLd, raw, c, hsz, hh, hbl, hde, hdeE, hrepC, -⟩ :=
      Claim.load_verified_constant_de ⟨br, hbr, rfl⟩ evLd
    have hrec : recordOf E₀ (Core.ixAddr br) = some c := by
      rw [← hbl]
      exact Claim.recordOf_hashed hS hH (Core.hashed_mono hsub12 hh) hsz hde hdeE
    have hbrCi := Bytes.repAddressRef_heapMono₂ Core.addrTy extLd hbr
    obtain ⟨-, hpr, b_own, hownRep, hownEq⟩ :=
      projection_block_claim_spec (a := Core.ixAddr br) (Claim.RepConstant.mono evCi.heap_extends hrepC) evPb
    have extPb : Heap.Extends h m_pb := extLd.trans (evCi.heap_extends.trans evPb.heap_extends)
    have hpos := ref_projects_from_spec hS hH hcib hsmall c_ib.refs.toList 0 (by simp)
      (RepLinkedList.mono Claim.repAddrElem_heapMono₂ extPb hrefs)
      (RepLinkedList.mono (fun _ _ _ _ _ r => r) extPb hused)
      ⟨b_own, hownRep, rfl⟩ (by simpa using evRpf) hsubRpf
    have husedNil := proj_usedRefIdxs_nil hS hbrCi evCi hsubCi hrec hpr
    obtain ⟨cb, hcb, hca⟩ := Claim.proj_member_of_load hS hH hbrCi evCi hsubCi hrec hpr
    rw [← hownEq] at hcb hca
    exact ⟨Core.ixAddr b_own, c, cb, hpos, hrec, hpr, hownEq.symm, husedNil, hcb, hca⟩
  match Obs.«KernelModeled::projection_of_ref_block».obs ev with
  | .IPrj (cs12 := cs12) (cs_skilefqi := csCi) (cs93 := csRpf)
      (ev14 := evLd) (ev_pvplyepc := evCi) (ev_bdycolxp := evPb) (ev95 := evRpf)
      (hc140 := hcs) .. =>
    exact hcase evLd evCi evPb evRpf
      (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
      (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
      (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
  | .CPrj (cs12 := cs12) (cs_tafpebbo := csCi) (cs157 := csRpf)
      (ev14 := evLd) (ev_rnaxgwez := evCi) (ev_mecagwun := evPb) (ev159 := evRpf)
      (hc204 := hcs) .. =>
    exact hcase evLd evCi evPb evRpf
      (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
      (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
      (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
  | .other (he209 := h0) .. => exact absurd (Value.field.inj h0) one_ne_zero

/-- **`KernelModeled::projection_of_advice`**: returning `1` witnesses that `r` is an
`IPrj`/`CPrj` of some `blk ∈ S`, with `usedRefIdxs = []` and `ConstAddrOf`. -/
theorem projection_of_advice_spec {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {r : _root_.Address} {S : List _root_.Address} {x_r x_aset : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hr : Core.S0.addr h x_r r) (hSrep : Claim.RepAddrSet h S x_aset)
    (ev : ObsFn Obs.W "KernelModeled::projection_of_advice" [x_r, x_aset] h (.field 1) h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∃ blk c cb, blk ∈ S ∧ recordOf E₀ r = some c ∧ IsProj c ∧
      Ix.Cert.ownerOf r c = blk ∧ usedRefIdxs c = [] ∧
      recordOf E₀ blk = some cb ∧ ConstAddrOf blk cb r := by
  obtain ⟨br, hbr, rfl⟩ := hr
  have hcase : ∀ {m2 m_ci m_pb : Heap F} {v_ci v_pb : SourceValue F}
      {cs12 cs_ci cs_pb cs_mem : List (Call F)} {vC : SourceValue F},
      ObsFn Obs.W "Ingress::load_verified_constant" [x_r] h vC m2 cs12 →
      ObsFn Obs.W "Ingress::get_ci" [x_r] m2 v_ci m_ci cs_ci →
      ObsFn Obs.W "KernelModeled::projection_block" [vC] m_ci v_pb m_pb cs_pb →
      ObsFn Obs.W "KernelClaim::addr_set_member" [v_pb, x_aset] m_pb (.field 1) h' cs_mem →
      (∀ cl ∈ cs12, cl ∈ calls) → (∀ cl ∈ cs_ci, cl ∈ calls) →
      ∃ blk c cb, blk ∈ S ∧ recordOf E₀ (Core.ixAddr br) = some c ∧ IsProj c ∧
        Ix.Cert.ownerOf (Core.ixAddr br) c = blk ∧ usedRefIdxs c = [] ∧
        recordOf E₀ blk = some cb ∧ ConstAddrOf blk cb (Core.ixAddr br) := by
    intro m2 m_ci m_pb v_ci v_pb cs12 cs_ci cs_pb cs_mem vC evLd evCi evPb evMem hsub12 hsubCi
    obtain ⟨extLd, raw, c, hsz, hh, hbl, hde, hdeE, hrepC, -⟩ :=
      Claim.load_verified_constant_de ⟨br, hbr, rfl⟩ evLd
    have hrec : recordOf E₀ (Core.ixAddr br) = some c := by
      rw [← hbl]
      exact Claim.recordOf_hashed hS hH (Core.hashed_mono hsub12 hh) hsz hde hdeE
    have hbrCi := Bytes.repAddressRef_heapMono₂ Core.addrTy extLd hbr
    obtain ⟨-, hpr, b_own, hownRep, hownEq⟩ :=
      projection_block_claim_spec (a := Core.ixAddr br) (Claim.RepConstant.mono evCi.heap_extends hrepC) evPb
    have extPb : Heap.Extends h m_pb := extLd.trans (evCi.heap_extends.trans evPb.heap_extends)
    obtain ⟨hmem, -⟩ := Claim.addr_set_member_set_spec hownRep (hSrep.mono extPb) evMem
    have husedNil := proj_usedRefIdxs_nil hS hbrCi evCi hsubCi hrec hpr
    obtain ⟨cb, hcb, hca⟩ := Claim.proj_member_of_load hS hH hbrCi evCi hsubCi hrec hpr
    rw [← hownEq] at hcb hca
    exact ⟨Core.ixAddr b_own, c, cb, hmem rfl, hrec, hpr, hownEq.symm, husedNil, hcb, hca⟩
  match Obs.«KernelModeled::projection_of_advice».obs ev with
  | .IPrj (cs12 := cs12) (cs_skilefqi := csCi) (ev14 := evLd) (ev_pvplyepc := evCi)
      (ev109 := evPb) (ev95 := evMem) (hc125 := hcs) .. =>
    exact hcase evLd evCi evPb evMem
      (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
      (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
  | .CPrj (cs12 := cs12) (cs_tafpebbo := csCi) (ev14 := evLd) (ev_rnaxgwez := evCi)
      (ev158 := evPb) (ev144 := evMem) (hc174 := hcs) .. =>
    exact hcase evLd evCi evPb evMem
      (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
      (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
  | .other (he179 := h0) .. => exact absurd (Value.field.inj h0) one_ne_zero

/-! ## `family_refs_ok` specification -/

private theorem family_refs_go_spec {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {B rb : _root_.Address} {cB crb : Ixon.Constant} {W : List _root_.Address}
    (hcB : recordOf E₀ B = some cB) (hBsmall : cB.refs.size < 8589934592)
    (hcrb : recordOf E₀ rb = some crb) (hrbSmall : crb.refs.size < 8589934592) :
    ∀ (xs : List _root_.Address) (i : Nat)
      {x_rc x_refs x_used x_blk x_irefs x_iused x_wset r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      crb.refs.toList.drop i = xs →
      RepList Core.addrListEnum Claim.RepAddrElem h xs x_refs →
      RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h (Core.S0.usedRefIdxs crb) x_used →
      Core.S0.addr h x_blk B →
      RepList Core.addrListEnum Claim.RepAddrElem h cB.refs.toList x_irefs →
      RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h (Core.S0.usedRefIdxs cB) x_iused →
      Claim.RepAddrSet h W x_wset →
      ObsFn Obs.W "KernelModeled::family_refs_go"
        [x_rc, x_refs, x_used, .field (i : F), x_blk, x_irefs, x_iused, x_wset] h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∀ j, i ≤ j → j ∈ usedRefIdxs crb → ∀ ref, crb.refs[j]? = some ref →
        UsedRef E₀ B ref ∨
        (∃ c cb, recordOf E₀ ref = some c ∧ IsProj c ∧ Ix.Cert.ownerOf ref c = B ∧
          usedRefIdxs c = [] ∧ recordOf E₀ B = some cb ∧ ConstAddrOf B cb ref) ∨
        (∃ blk c cb, PathPos E₀ B blk ∧ recordOf E₀ ref = some c ∧ IsProj c ∧
          Ix.Cert.ownerOf ref c = blk ∧ usedRefIdxs c = [] ∧
          recordOf E₀ blk = some cb ∧ ConstAddrOf blk cb ref) ∨
        ref ∈ W
  | [], i, x_rc, x_refs, x_used, x_blk, x_irefs, x_iused, x_wset, r, h, h', cs,
      hdrop, _, _, _, _, _, _, _, _ => by
    intro j hij _ ref href
    have hge : crb.refs.toList.length ≤ i := List.drop_eq_nil_iff.mp hdrop
    rw [← Array.getElem?_toList] at href
    have hlt := (List.getElem?_eq_some_iff.mp href).1
    omega
  | a :: rest, i, x_rc, x_refs, x_used, x_blk, x_irefs, x_iused, x_wset, r, h, h', cs,
      hdrop, hrefs, hused, hblk, hirefs, hiused, hwset, ev, hsub => by
    have hiLt : i < crb.refs.size := by
      have hne : crb.refs.toList.drop i ≠ [] := by rw [hdrop]; simp
      have : i < crb.refs.toList.length := by
        by_contra hge; exact hne (List.drop_eq_nil_iff.mpr (by omega))
      simpa using this
    have hiBound : i < 72057594037927936 := by omega
    match Obs.«KernelModeled::family_refs_go».obs ev with
    | .Nil (ld12 := ld) .. => exact absurd (Lib.rep_nil_of_load hrefs ld) (by simp)
    | .Cons (x_r := x_r) (m385 := m385) (cs387 := csSg) (cs396 := csRec)
        (ld12 := ld) (sg392 := sg) (op_gskedpnl := opAdd) (ev398 := evRec) (hc463 := hcs) .. =>
      obtain ⟨a', rest', he, haAddr, hrestRep⟩ := Lib.rep_cons_of_load hrefs ld
      injection he with ha' hrest'
      subst ha' hrest'
      have hsubSg : ∀ cl ∈ csSg, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hsubRec : ∀ cl ∈ csRec, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have haSpec : Heap.Extends h m385 ∧
          (i ∈ usedRefIdxs crb →
            UsedRef E₀ B a ∨
            (∃ c cb, recordOf E₀ a = some c ∧ IsProj c ∧ Ix.Cert.ownerOf a c = B ∧
              usedRefIdxs c = [] ∧ recordOf E₀ B = some cb ∧ ConstAddrOf B cb a) ∨
            (∃ blk c cb, PathPos E₀ B blk ∧ recordOf E₀ a = some c ∧ IsProj c ∧
              Ix.Cert.ownerOf a c = blk ∧ usedRefIdxs c = [] ∧
              recordOf E₀ blk = some cb ∧ ConstAddrOf blk cb a) ∨
            a ∈ W) := by
        -- helper for `IPrj`/`CPrj` own-block match
        have hownMatch : ∀ {m86 m_ld m_ci m_pb m_eq : Heap F} {vC v_ci v_pb : SourceValue F}
            {cs_ld cs_ci cs_pb cs_eq : List (Call F)},
            Heap.Extends h m86 →
            ObsFn Obs.W "Ingress::load_verified_constant" [x_r] m86 vC m_ld cs_ld →
            ObsFn Obs.W "Ingress::get_ci" [x_r] m_ld v_ci m_ci cs_ci →
            ObsFn Obs.W "KernelModeled::projection_block" [vC] m_ci v_pb m_pb cs_pb →
            ObsFn Obs.W "Bytes::address_eq" [v_pb, x_blk] m_pb (.field 1) m_eq cs_eq →
            (∀ cl ∈ cs_ld, cl ∈ calls) → (∀ cl ∈ cs_ci, cl ∈ calls) →
            ∃ c cb, recordOf E₀ a = some c ∧ IsProj c ∧ Ix.Cert.ownerOf a c = B ∧
              usedRefIdxs c = [] ∧ recordOf E₀ B = some cb ∧ ConstAddrOf B cb a := by
          intro m86 m_ld m_ci m_pb m_eq vC v_ci v_pb cs_ld cs_ci cs_pb cs_eq
            ext86 evLd evCi evPb evEq hsubLd hsubCi
          obtain ⟨ba, hba, rfl⟩ := haAddr
          obtain ⟨bB, hbB, rfl⟩ := hblk
          have hba86 := Bytes.repAddressRef_heapMono₂ Core.addrTy ext86 hba
          obtain ⟨extLd, raw, c, hsz, hh, hbl, hde, hdeE, hrepC, -⟩ :=
            Claim.load_verified_constant_de ⟨ba, hba86, rfl⟩ evLd
          have hrec : recordOf E₀ (Core.ixAddr ba) = some c := by
            rw [← hbl]
            exact Claim.recordOf_hashed hS hH (Core.hashed_mono hsubLd hh) hsz hde hdeE
          have hbaCi := Bytes.repAddressRef_heapMono₂ Core.addrTy extLd hba86
          obtain ⟨-, hpr, b_own, hownRep, hownEq⟩ :=
            projection_block_claim_spec (a := Core.ixAddr ba)
              (Claim.RepConstant.mono evCi.heap_extends hrepC) evPb
          have hbBPb := Bytes.repAddressRef_heapMono₂ Core.addrTy
            (ext86.trans (extLd.trans (evCi.heap_extends.trans evPb.heap_extends))) hbB
          obtain ⟨heqV, -⟩ := Lib.address_eq_spec evEq hownRep hbBPb
          have eb : b_own = bB := by
            by_cases hne : b_own = bB
            · exact hne
            · simp [hne] at heqV
          subst eb
          have husedNil := proj_usedRefIdxs_nil hS hbaCi evCi hsubCi hrec hpr
          obtain ⟨cb, hcb, hca⟩ := Claim.proj_member_of_load hS hH hbaCi evCi hsubCi hrec hpr
          rw [← hownEq] at hcb hca
          exact ⟨c, cb, hrec, hpr, hownEq.symm, husedNil, hcb, hca⟩
        match sg with
        | .n1_n1 (ev56 := evHas) (ev99 := evUrh) (he165 := hh) .. =>
          refine ⟨by rw [hh]; exact evHas.heap_extends.trans evUrh.heap_extends, fun _ => ?_⟩
          exact Or.inl (used_ref_has_spec hcB hBsmall cB.refs.toList 0 (by simp)
            (RepLinkedList.mono Claim.repAddrElem_heapMono₂ evHas.heap_extends hirefs)
            (RepLinkedList.mono (fun _ _ _ _ _ r => r) evHas.heap_extends hiused)
            (Core.S0.addr_mono evHas.heap_extends haAddr) (by simpa using evUrh))
        | .n1_other_IPrj_n1 (cs_zdnxjwry := csLd) (cs_qbnwdknq := csCi)
            (ev56 := e1) (ev99 := e2) (ev_xluoudzn := evLd) (ev_qgckrtca := evCi)
            (ev_vtyrtvpa := evPb) (ev_tnredfpp := evEq) (he_bzceqiro := hh) (hc_zgauihwq := hcsS) .. =>
          have ext86 := e1.heap_extends.trans e2.heap_extends
          refine ⟨by rw [hh]; exact ext86.trans (evLd.heap_extends.trans
            (evCi.heap_extends.trans (evPb.heap_extends.trans evEq.heap_extends))), fun _ => ?_⟩
          exact Or.inr (Or.inl (hownMatch ext86 evLd evCi evPb evEq
            (fun cl hcl => hsubSg cl (by rw [hcsS]; simp [hcl]))
            (fun cl hcl => hsubSg cl (by rw [hcsS]; simp [hcl]))))
        | .n1_other_IPrj_other_n1 (cs_snsikqdv := csPrb)
            (ev56 := e1) (ev99 := e2) (ev_xluoudzn := e3) (ev_qgckrtca := e4)
            (ev_vtyrtvpa := e5) (ev_tnredfpp := e6) (ev_yzpcnxhb := evPrb)
            (he_zrgpsvav := hh) (hc_azxcvjxu := hcsS) .. =>
          have ext6 := e1.heap_extends.trans (e2.heap_extends.trans (e3.heap_extends.trans
            (e4.heap_extends.trans (e5.heap_extends.trans e6.heap_extends))))
          refine ⟨by rw [hh]; exact ext6.trans evPrb.heap_extends, fun _ => ?_⟩
          exact Or.inr (Or.inr (Or.inl (projection_of_ref_block_spec hS hH hcB hBsmall
            (Core.S0.addr_mono ext6 haAddr)
            (RepLinkedList.mono Claim.repAddrElem_heapMono₂ ext6 hirefs)
            (RepLinkedList.mono (fun _ _ _ _ _ r => r) ext6 hiused)
            evPrb (fun cl hcl => hsubSg cl (by rw [hcsS]; simp [hcl])))))
        | .n1_other_IPrj_other_other (ev56 := e1) (ev99 := e2) (ev_xluoudzn := e3)
            (ev_qgckrtca := e4) (ev_vtyrtvpa := e5) (ev_tnredfpp := e6) (ev_yzpcnxhb := e7)
            (ev_vlqtvrdt := evMem) (heq_cgphyymq := h1) (he_qwbsdwlv := hh) .. =>
          have ext7 := e1.heap_extends.trans (e2.heap_extends.trans (e3.heap_extends.trans
            (e4.heap_extends.trans (e5.heap_extends.trans (e6.heap_extends.trans e7.heap_extends)))))
          refine ⟨by rw [hh]; exact ext7.trans evMem.heap_extends, fun _ => ?_⟩
          obtain ⟨ba, hba, rfl⟩ := haAddr
          obtain ⟨hmem, -⟩ := Claim.addr_set_member_set_spec
            (Bytes.repAddressRef_heapMono₂ Core.addrTy ext7 hba) (hwset.mono ext7) evMem
          exact Or.inr (Or.inr (Or.inr (hmem h1)))
        | .n1_other_CPrj_n1 (cs_zdnxjwry := csLd) (cs_lpudusuv := csCi)
            (ev56 := e1) (ev99 := e2) (ev_xluoudzn := evLd) (ev_adpdzihl := evCi)
            (ev_jzuzvoks := evPb) (ev_glaclyhi := evEq) (he_nmfyxnwl := hh) (hc_xipxbqsc := hcsS) .. =>
          have ext86 := e1.heap_extends.trans e2.heap_extends
          refine ⟨by rw [hh]; exact ext86.trans (evLd.heap_extends.trans
            (evCi.heap_extends.trans (evPb.heap_extends.trans evEq.heap_extends))), fun _ => ?_⟩
          exact Or.inr (Or.inl (hownMatch ext86 evLd evCi evPb evEq
            (fun cl hcl => hsubSg cl (by rw [hcsS]; simp [hcl]))
            (fun cl hcl => hsubSg cl (by rw [hcsS]; simp [hcl]))))
        | .n1_other_CPrj_other_n1 (cs_owbqhnqq := csPrb)
            (ev56 := e1) (ev99 := e2) (ev_xluoudzn := e3) (ev_adpdzihl := e4)
            (ev_jzuzvoks := e5) (ev_glaclyhi := e6) (ev_ajdyfujx := evPrb)
            (he_lgylpqds := hh) (hc_aythwrab := hcsS) .. =>
          have ext6 := e1.heap_extends.trans (e2.heap_extends.trans (e3.heap_extends.trans
            (e4.heap_extends.trans (e5.heap_extends.trans e6.heap_extends))))
          refine ⟨by rw [hh]; exact ext6.trans evPrb.heap_extends, fun _ => ?_⟩
          exact Or.inr (Or.inr (Or.inl (projection_of_ref_block_spec hS hH hcB hBsmall
            (Core.S0.addr_mono ext6 haAddr)
            (RepLinkedList.mono Claim.repAddrElem_heapMono₂ ext6 hirefs)
            (RepLinkedList.mono (fun _ _ _ _ _ r => r) ext6 hiused)
            evPrb (fun cl hcl => hsubSg cl (by rw [hcsS]; simp [hcl])))))
        | .n1_other_CPrj_other_other (ev56 := e1) (ev99 := e2) (ev_xluoudzn := e3)
            (ev_adpdzihl := e4) (ev_jzuzvoks := e5) (ev_glaclyhi := e6) (ev_ajdyfujx := e7)
            (ev_evifbzkm := evMem) (heq_qygjpayn := h1) (he_vykzghpw := hh) .. =>
          have ext7 := e1.heap_extends.trans (e2.heap_extends.trans (e3.heap_extends.trans
            (e4.heap_extends.trans (e5.heap_extends.trans (e6.heap_extends.trans e7.heap_extends)))))
          refine ⟨by rw [hh]; exact ext7.trans evMem.heap_extends, fun _ => ?_⟩
          obtain ⟨ba, hba, rfl⟩ := haAddr
          obtain ⟨hmem, -⟩ := Claim.addr_set_member_set_spec
            (Bytes.repAddressRef_heapMono₂ Core.addrTy ext7 hba) (hwset.mono ext7) evMem
          exact Or.inr (Or.inr (Or.inr (hmem h1)))
        | .n1_other_other_other_n1 (cs_wknojnhr := csPrb)
            (ev56 := e1) (ev99 := e2) (ev_xluoudzn := e3) (ev_jlgopmei := evPrb)
            (he_tzsimcbf := hh) (hc_iowtuhxz := hcsS) .. =>
          have ext3 := e1.heap_extends.trans (e2.heap_extends.trans e3.heap_extends)
          refine ⟨by rw [hh]; exact ext3.trans evPrb.heap_extends, fun _ => ?_⟩
          exact Or.inr (Or.inr (Or.inl (projection_of_ref_block_spec hS hH hcB hBsmall
            (Core.S0.addr_mono ext3 haAddr)
            (RepLinkedList.mono Claim.repAddrElem_heapMono₂ ext3 hirefs)
            (RepLinkedList.mono (fun _ _ _ _ _ r => r) ext3 hiused)
            evPrb (fun cl hcl => hsubSg cl (by rw [hcsS]; simp [hcl])))))
        | .n1_other_other_other_other (ev56 := e1) (ev99 := e2) (ev_xluoudzn := e3)
            (ev_jlgopmei := e4) (ev_aamioxen := evMem) (heq_siovpfty := h1)
            (he_mczqspon := hh) .. =>
          have ext4 := e1.heap_extends.trans (e2.heap_extends.trans
            (e3.heap_extends.trans e4.heap_extends))
          refine ⟨by rw [hh]; exact ext4.trans evMem.heap_extends, fun _ => ?_⟩
          obtain ⟨ba, hba, rfl⟩ := haAddr
          obtain ⟨hmem, -⟩ := Claim.addr_set_member_set_spec
            (Bytes.repAddressRef_heapMono₂ Core.addrTy ext4 hba) (hwset.mono ext4) evMem
          exact Or.inr (Or.inr (Or.inr (hmem h1)))
        | .other (ev56 := evHas) (hne375 := hne1) (he382 := hh) .. =>
          refine ⟨by rw [hh]; exact evHas.heap_extends, fun hi => ?_⟩
          have h1 := (Claim.g_list_has_spec (Core.S0.usedRefIdxs crb) hiBound hused evHas).2.mpr
            (by rwa [Assembly.usedRefIdxs_eq])
          exact (hne1 h1).elim
      obtain ⟨extSg, haCls⟩ := haSpec
      simp only [evalBinOp, Except.ok.injEq] at opAdd
      subst opAdd
      have hcast : ((i : F) + 1) = ((i + 1 : Nat) : F) := by push_cast; rfl
      rw [hcast] at evRec
      have hdrop1 : crb.refs.toList.drop (i + 1) = rest := by
        have h1 : (crb.refs.toList.drop i).tail = crb.refs.toList.drop (i + 1) := by
          rw [List.tail_drop]
        rw [← h1, hdrop]; rfl
      have hrecCls := family_refs_go_spec hS hH hcB hBsmall hcrb hrbSmall rest (i + 1) hdrop1
        (RepLinkedList.mono Claim.repAddrElem_heapMono₂ extSg hrestRep)
        (RepLinkedList.mono (fun _ _ _ _ _ r => r) extSg hused)
        (Core.S0.addr_mono extSg hblk)
        (RepLinkedList.mono Claim.repAddrElem_heapMono₂ extSg hirefs)
        (RepLinkedList.mono (fun _ _ _ _ _ r => r) extSg hiused)
        (hwset.mono extSg) evRec hsubRec
      intro j hij hj ref href
      by_cases hji : j = i
      · subst hji
        have haEq : ref = a := by
          rw [← Array.getElem?_toList, ← List.head?_drop, hdrop] at href
          exact (Option.some.inj href).symm
        subst haEq
        exact haCls hj
      · exact hrecCls j (by omega) hj ref href

/-- **`KernelModeled::family_refs_ok`**: every used reference `ref` of `rb` satisfies
`NotBlockIn`, `OpOrderedAt`, `¬ CoveredAt → SourceSafe`, and the 4-way classification relative to
`B` and the witness set `W`. -/
theorem family_refs_ok_spec {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {B rb : _root_.Address} {W : List _root_.Address}
    {x_rc x_rb x_blk x_wset r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrc : Claim.RCLimRep t bAddr lim h x_rc)
    (hrb : Core.S0.addr h x_rb rb) (hblk : Core.S0.addr h x_blk B)
    (hwset : Claim.RepAddrSet h W x_wset)
    (ev : ObsFn Obs.W "KernelModeled::family_refs_ok" [x_rc, x_rb, x_blk, x_wset] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∀ ref, UsedRef E₀ rb ref →
      Claim.NotBlockIn calls ref ∧ Claim.OpOrderedAt t lim ref ∧
      (¬ Claim.CoveredAt t lim ref → Claim.SourceSafe E₀ ref) ∧
      (UsedRef E₀ B ref ∨
        (∃ c cb, recordOf E₀ ref = some c ∧ IsProj c ∧ Ix.Cert.ownerOf ref c = B ∧
          usedRefIdxs c = [] ∧ recordOf E₀ B = some cb ∧ ConstAddrOf B cb ref) ∨
        (∃ blk c cb, PathPos E₀ B blk ∧ recordOf E₀ ref = some c ∧ IsProj c ∧
          Ix.Cert.ownerOf ref c = blk ∧ usedRefIdxs c = [] ∧
          recordOf E₀ blk = some cb ∧ ConstAddrOf blk cb ref) ∨
        ref ∈ W) := by
  match Obs.«KernelModeled::family_refs_ok».obs ev with
  | .run (cs12 := cs12) (cs34 := cs34) (x_refs := x_refs) (x_irefs := x_irefs)
      (cs_ijcbjcgc := csGo) (cs_zlhtmzlz := csSafe)
      (ev14 := evRb) (ev36 := evB) (ev_ycrqbsja := evIdxsRb) (ev_nhomjxfq := evIdxsB)
      (ev_kfwmaaqi := evGo) (ev_ozxzdina := evIdxsRb2) (ev_tnqzszcy := evSafe)
      (hc222 := hcs) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsub34 : ∀ cl ∈ cs34, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsubGo : ∀ cl ∈ csGo, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsubSafe : ∀ cl ∈ csSafe, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    obtain ⟨extRb, rawRb, crb, hszRb, hhRb, hblRb, hdeRb, hdeERb, hrepRb, -⟩ :=
      Claim.load_verified_constant_de hrb evRb
    have hcrb : recordOf E₀ rb = some crb := by
      rw [← hblRb]
      exact Claim.recordOf_hashed hS hH (Core.hashed_mono hsub12 hhRb) hszRb hdeRb hdeERb
    have hrbSmall := refs_small_of_decoded hszRb hdeERb
    obtain ⟨extB, rawB, cB, hszB, hhB, hblB, hdeB, hdeEB, hrepB, -⟩ :=
      Claim.load_verified_constant_de (Core.S0.addr_mono extRb hblk) evB
    have hcB : recordOf E₀ B = some cB := by
      rw [← hblB]
      exact Claim.recordOf_hashed hS hH (Core.hashed_mono hsub34 hhB) hszB hdeB hdeEB
    have hBsmall := refs_small_of_decoded hszB hdeEB
    have hrepRb2 := Claim.RepConstant.mono extB hrepRb
    obtain ⟨extI1, hidxsRb⟩ := Claim.const_idxs_of_spec hrepRb2 evIdxsRb
    obtain ⟨extI2, hidxsB⟩ := Claim.const_idxs_of_spec (Claim.RepConstant.mono extI1 hrepB) evIdxsB
    obtain ⟨_, _, rpRb, _, _, hmkRb, _, _, hrefsRb, _, _⟩ := id hrepRb2
    injection hmkRb with _ _ haRb; simp only [List.cons.injEq] at haRb
    obtain ⟨-, -, rfl, -⟩ := haRb
    obtain ⟨_, _, rpB, _, _, hmkB, -, -, hrefsB, -, -⟩ := hrepB
    injection hmkB with _ _ haB; simp only [List.cons.injEq] at haB
    obtain ⟨-, -, rfl, -⟩ := haB
    have extGo0 : Heap.Extends h _ := extRb.trans (extB.trans (extI1.trans extI2))
    have hgo := family_refs_go_spec hS hH hcB hBsmall hcrb hrbSmall crb.refs.toList 0 (by simp)
      (RepLinkedList.mono Claim.repAddrElem_heapMono₂ (extI1.trans extI2) hrefsRb)
      (RepLinkedList.mono (fun _ _ _ _ _ r => r) extI2 hidxsRb)
      (Core.S0.addr_mono extGo0 hblk)
      (RepLinkedList.mono Claim.repAddrElem_heapMono₂ (extI1.trans extI2) hrefsB)
      hidxsB (hwset.mono extGo0) (by simpa using evGo) hsubGo
    have extGo1 : Heap.Extends _ _ := (extI1.trans extI2).trans evGo.heap_extends
    obtain ⟨extI3, hidxsRb2⟩ := Claim.const_idxs_of_spec
      (Claim.RepConstant.mono extGo1 hrepRb2) evIdxsRb2
    have hsafe := assert_inner_refs_safe_spec hS hrbSmall
      (hrc.mono (extGo0.trans (evGo.heap_extends.trans extI3)))
      (RepLinkedList.mono Claim.repAddrElem_heapMono₂ (extGo1.trans extI3) hrefsRb)
      hidxsRb2 evSafe hsubSafe
    intro ref ⟨crb', j, hcrb', hj, href⟩
    have ec : crb' = crb := Option.some.inj (hcrb'.symm.trans hcrb)
    subst crb'
    obtain ⟨-, hcovSafe, hnb, hord⟩ := hsafe j hj ref href
    exact ⟨hnb, hord, hcovSafe, hgo j (Nat.zero_le j) hj ref href⟩

/-! ## `check_advice_records` indexed specification -/

private theorem advice_refs_ok_spec {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {a : _root_.Address} {ca : Ixon.Constant} {S W : List _root_.Address}
    (hca : recordOf E₀ a = some ca) (hasmall : ca.refs.size < 8589934592) :
    ∀ (xs : List _root_.Address) (i : Nat)
      {x_refs x_used x_aset x_wset r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ca.refs.toList.drop i = xs →
      RepList Core.addrListEnum Claim.RepAddrElem h xs x_refs →
      RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h (Core.S0.usedRefIdxs ca) x_used →
      Claim.RepAddrSet h S x_aset →
      Claim.RepAddrSet h W x_wset →
      ObsFn Obs.W "KernelModeled::advice_refs_ok"
        [x_refs, x_used, .field (i : F), x_aset, x_wset] h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∀ j, i ≤ j → j ∈ usedRefIdxs ca → ∀ ref, ca.refs[j]? = some ref →
        ref ∈ S ∨ ref ∈ W ∨
        (∃ blk c cb, blk ∈ S ∧ recordOf E₀ ref = some c ∧ IsProj c ∧
          Ix.Cert.ownerOf ref c = blk ∧ usedRefIdxs c = [] ∧
          recordOf E₀ blk = some cb ∧ ConstAddrOf blk cb ref)
  | [], i, _, _, _, _, _, _, _, _, hdrop, _, _, _, _, _, _ => by
    intro j hij _ ref href
    have hge : ca.refs.toList.length ≤ i := List.drop_eq_nil_iff.mp hdrop
    rw [← Array.getElem?_toList] at href
    have hlt := (List.getElem?_eq_some_iff.mp href).1
    omega
  | r0 :: rest, i, x_refs, x_used, x_aset, x_wset, r, h, h', cs,
      hdrop, hrefs, hused, haset, hwset, ev, hsub => by
    have hiLt : i < ca.refs.size := by
      have hne : ca.refs.toList.drop i ≠ [] := by rw [hdrop]; simp
      have : i < ca.refs.toList.length := by
        by_contra hge; exact hne (List.drop_eq_nil_iff.mpr (by omega))
      simpa using this
    have hiBound : i < 72057594037927936 := by omega
    match Obs.«KernelModeled::advice_refs_ok».obs ev with
    | .Nil (ld12 := ld) .. => exact absurd (Lib.rep_nil_of_load hrefs ld) (by simp)
    | .Cons (m291 := m291) (cs293 := csSg) (cs302 := csRec)
        (ld12 := ld) (sg298 := sg) (op337 := opAdd) (ev304 := evRec) (hc353 := hcs) .. =>
      obtain ⟨r0', rest', he, hr0Addr, hrestRep⟩ := Lib.rep_cons_of_load hrefs ld
      injection he with hr0' hrest'
      subst hr0' hrest'
      have hsubSg : ∀ cl ∈ csSg, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hsubRec : ∀ cl ∈ csRec, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hr0Spec : Heap.Extends h m291 ∧
          (i ∈ usedRefIdxs ca →
            r0 ∈ S ∨ r0 ∈ W ∨
            (∃ blk c cb, blk ∈ S ∧ recordOf E₀ r0 = some c ∧ IsProj c ∧
              Ix.Cert.ownerOf r0 c = blk ∧ usedRefIdxs c = [] ∧
              recordOf E₀ blk = some cb ∧ ConstAddrOf blk cb r0)) := by
        match sg with
        | .n1_n1 (ev56 := e1) (ev99 := evMem) (he150 := hh) .. =>
          refine ⟨by rw [hh]; exact e1.heap_extends.trans evMem.heap_extends, fun _ => ?_⟩
          obtain ⟨br, hbr, rfl⟩ := hr0Addr
          obtain ⟨hm, -⟩ := Claim.addr_set_member_set_spec
            (Bytes.repAddressRef_heapMono₂ Core.addrTy e1.heap_extends hbr)
            (haset.mono e1.heap_extends) evMem
          exact Or.inl (hm rfl)
        | .n1_other_n1 (ev56 := e1) (ev99 := e2) (ev170 := evMem) (he221 := hh) .. =>
          have ext2 := e1.heap_extends.trans e2.heap_extends
          refine ⟨by rw [hh]; exact ext2.trans evMem.heap_extends, fun _ => ?_⟩
          obtain ⟨br, hbr, rfl⟩ := hr0Addr
          obtain ⟨hm, -⟩ := Claim.addr_set_member_set_spec
            (Bytes.repAddressRef_heapMono₂ Core.addrTy ext2 hbr) (hwset.mono ext2) evMem
          exact Or.inr (Or.inl (hm rfl))
        | .n1_other_other (cs230 := csPa) (ev56 := e1) (ev99 := e2) (ev170 := e3)
            (ev232 := evPa) (heq275 := h1) (he279 := hh) (hc280 := hcsS) .. =>
          have ext3 := e1.heap_extends.trans (e2.heap_extends.trans e3.heap_extends)
          refine ⟨by rw [hh]; exact ext3.trans evPa.heap_extends, fun _ => ?_⟩
          rw [h1] at evPa
          exact Or.inr (Or.inr (projection_of_advice_spec hS hH
            (Core.S0.addr_mono ext3 hr0Addr) (haset.mono ext3) evPa
            (fun cl hcl => hsubSg cl (by rw [hcsS]; simp [hcl]))))
        | .other (ev56 := evHas) (hne281 := hne1) (he288 := hh) .. =>
          refine ⟨by rw [hh]; exact evHas.heap_extends, fun hi => ?_⟩
          have h1 := (Claim.g_list_has_spec (Core.S0.usedRefIdxs ca) hiBound hused evHas).2.mpr
            (by rwa [Assembly.usedRefIdxs_eq])
          exact (hne1 h1).elim
      obtain ⟨extSg, hr0Cls⟩ := hr0Spec
      simp only [evalBinOp, Except.ok.injEq] at opAdd
      subst opAdd
      have hcast : ((i : F) + 1) = ((i + 1 : Nat) : F) := by push_cast; rfl
      rw [hcast] at evRec
      have hdrop1 : ca.refs.toList.drop (i + 1) = rest := by
        have h1 : (ca.refs.toList.drop i).tail = ca.refs.toList.drop (i + 1) := by
          rw [List.tail_drop]
        rw [← h1, hdrop]; rfl
      have hrecCls := advice_refs_ok_spec hS hH hca hasmall rest (i + 1) hdrop1
        (RepLinkedList.mono Claim.repAddrElem_heapMono₂ extSg hrestRep)
        (RepLinkedList.mono (fun _ _ _ _ _ r => r) extSg hused)
        (haset.mono extSg) (hwset.mono extSg) evRec hsubRec
      intro j hij hj ref href
      by_cases hji : j = i
      · subst hji
        have heq : ref = r0 := by
          rw [← Array.getElem?_toList, ← List.head?_drop, hdrop] at href
          exact (Option.some.inj href).symm
        subst heq
        exact hr0Cls hj
      · exact hrecCls j (by omega) hj ref href

/-- **Detailed facts for a single `KernelModeled::check_advice_record` call** with seen set `S`
and witness set `W`. -/
def AdviceRecordFacts (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (lim : Option Nat)
    (S W : List _root_.Address) (a : _root_.Address) : Prop :=
  Claim.OpOrderedAt t lim a ∧
  ∃ ca, recordOf E₀ a = some ca ∧ InLogic ca ∧
    -- Kind classification from `check_advice_record.Seg1`
    ((∃ d, ca.info = .defn d ∧ Claim.CheckedLimAt calls bAddr t a lim) ∨
      (∃ rc, ca.info = .recr rc ∧ Claim.CheckedLimAt calls bAddr t a lim) ∨
      (∃ ms, ca.info = .muts ms ∧
        (∀ m ∈ ms.toList, ∃ ind, m = .indc ind) ∧
        (∀ j, j < ms.size → Claim.MemberCheckedLimAt calls bAddr t a ms j lim) ∧
        Claim.NativeObsAt calls a) ∨
      (IsProj ca ∧ usedRefIdxs ca = [] ∧ Ix.Cert.ownerOf a ca ∈ S ∧
        ∃ cb, recordOf E₀ (Ix.Cert.ownerOf a ca) = some cb ∧
          ConstAddrOf (Ix.Cert.ownerOf a ca) cb a)) ∧
    -- Used-reference closure & inner-ref safety
    (∀ ref, UsedRef E₀ a ref →
      Claim.NotBlockIn calls ref ∧ Claim.OpOrderedAt t lim ref ∧
      (¬ Claim.CoveredAt t lim ref → Claim.SourceSafe E₀ ref) ∧
      (ref ∈ S ∨ ref ∈ W ∨
        (∃ blk c cb, blk ∈ S ∧ recordOf E₀ ref = some c ∧ IsProj c ∧
          Ix.Cert.ownerOf ref c = blk ∧ usedRefIdxs c = [] ∧
          recordOf E₀ blk = some cb ∧ ConstAddrOf blk cb ref)))

/-- **`KernelModeled::check_advice_record`** gives `AdviceRecordFacts`. -/
theorem check_advice_record_spec {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {ab : Bytes.Address} {S W : List _root_.Address}
    {x_rc x_a x_aset x_wset r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrc : Claim.RCLimRep t bAddr lim h x_rc)
    (ha : Bytes.RepAddressRef Core.addrTy h ab x_a)
    (haset : Claim.RepAddrSet h S x_aset)
    (hwset : Claim.RepAddrSet h W x_wset)
    (ev : ObsFn Obs.W "KernelModeled::check_advice_record" [x_rc, x_a, x_aset, x_wset] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    AdviceRecordFacts calls bAddr t E₀ lim S W (Core.ixAddr ab) := by
  have hlog : ∀ ca, recordOf E₀ (Core.ixAddr ab) = some ca → InLogic ca := by
    intro ca hca
    exact adviceCheck_logic t hS hH ⟨x_rc, x_a, x_aset, x_wset, r, h, h', cs,
      ab, ha, rfl, ev, hsub⟩ hca
  match Obs.«KernelModeled::check_advice_record».obs ev with
  | .run (m_judpcwze := m_ord) (m2 := m2) (cs12 := cs12) (x_info := x_info)
      (x_refs := x_refs) (m945 := m945) (cs947 := csSg) (cs_dkogjupv := csRefs) (cs_zlhtmzlz := csSafe)
      (ev_yqjbwijz := evOrd) (ev14 := evLd) (sg952 := sg)
      (ev_lawbyzgo := evIdxs1) (ev_bilbznow := evRefs) (ev_ozxzdina := evIdxs2)
      (ev_tnqzszcy := evSafe) (hc1011 := hcs) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsubSg : ∀ cl ∈ csSg, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsubRefs : ∀ cl ∈ csRefs, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsubSafe : ∀ cl ∈ csSafe, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hordA := assert_in_order_spec hrc ⟨ab, ha, rfl⟩ evOrd
    have haOrd := Bytes.repAddressRef_heapMono₂ Core.addrTy evOrd.heap_extends ha
    obtain ⟨extLd, raw, ca, hsz, hh, hbl, hde, hdeE, hrepC, -⟩ :=
      Claim.load_verified_constant_de ⟨ab, haOrd, rfl⟩ evLd
    have hca : recordOf E₀ (Core.ixAddr ab) = some ca := by
      rw [← hbl]
      exact Claim.recordOf_hashed hS hH (Core.hashed_mono hsub12 hh) hsz hde hdeE
    have hasmall := refs_small_of_decoded hsz hdeE
    have hcaLog := hlog ca hca
    have ext2 : Heap.Extends h m2 := evOrd.heap_extends.trans extLd
    obtain ⟨infoVal, _, rp, _, _, hmk, hinfoRep, _, hrefsRep, _, _⟩ := id hrepC
    injection hmk with _ _ hargs; simp only [List.cons.injEq] at hargs
    obtain ⟨rfl, -, rfl, -⟩ := hargs
    -- Extract `Heap.Extends m2 m945` and kind classification from `sg`
    have hkindSpec : Heap.Extends m2 m945 ∧
        ((∃ d, ca.info = .defn d ∧ Claim.CheckedLimAt calls bAddr t (Core.ixAddr ab) lim) ∨
          (∃ rc, ca.info = .recr rc ∧ Claim.CheckedLimAt calls bAddr t (Core.ixAddr ab) lim) ∨
          (∃ ms, ca.info = .muts ms ∧
            (∀ m ∈ ms.toList, ∃ ind, m = .indc ind) ∧
            (∀ j, j < ms.size → Claim.MemberCheckedLimAt calls bAddr t (Core.ixAddr ab) ms j lim) ∧
            Claim.NativeObsAt calls (Core.ixAddr ab)) ∨
          (IsProj ca ∧ usedRefIdxs ca = [] ∧ Ix.Cert.ownerOf (Core.ixAddr ab) ca ∈ S ∧
            ∃ cb, recordOf E₀ (Ix.Cert.ownerOf (Core.ixAddr ab) ca) = some cb ∧
              ConstAddrOf (Ix.Cert.ownerOf (Core.ixAddr ab) ca) cb (Core.ixAddr ab))) := by
      have hprojCase : ∀ {m_pb m_mem m_ci : Heap F} {vC v_pb v_ci : SourceValue F}
          {cs_pb cs_mem cs_ci : List (Call F)},
          Claim.RepConstant m2 ca vC →
          ObsFn Obs.W "KernelModeled::projection_block" [vC] m2 v_pb m_pb cs_pb →
          ObsFn Obs.W "KernelClaim::addr_set_member" [v_pb, x_aset] m_pb (.field 1) m_mem cs_mem →
          ObsFn Obs.W "Ingress::get_ci" [x_a] m_mem v_ci m_ci cs_ci →
          (∀ cl ∈ cs_ci, cl ∈ calls) →
          Heap.Extends m2 m_ci ∧
            (IsProj ca ∧ usedRefIdxs ca = [] ∧ Ix.Cert.ownerOf (Core.ixAddr ab) ca ∈ S ∧
              ∃ cb, recordOf E₀ (Ix.Cert.ownerOf (Core.ixAddr ab) ca) = some cb ∧
                ConstAddrOf (Ix.Cert.ownerOf (Core.ixAddr ab) ca) cb (Core.ixAddr ab)) := by
        intro m_pb m_mem m_ci vC v_pb v_ci cs_pb cs_mem cs_ci hvC evPb evMem evCi hsubCi
        obtain ⟨-, hpr, b_own, hownRep, hownEq⟩ :=
          projection_block_claim_spec (a := Core.ixAddr ab) hvC evPb
        obtain ⟨hmem, hmMem⟩ := Claim.addr_set_member_set_spec hownRep
          (haset.mono (ext2.trans evPb.heap_extends)) evMem
        have haCi := Bytes.repAddressRef_heapMono₂ Core.addrTy
          (ext2.trans (evPb.heap_extends.trans evMem.heap_extends)) ha
        have husedNil := proj_usedRefIdxs_nil hS haCi evCi hsubCi hca hpr
        obtain ⟨cb, hcb, hcaM⟩ := Claim.proj_member_of_load hS hH haCi evCi hsubCi hca hpr
        exact ⟨evPb.heap_extends.trans (evMem.heap_extends.trans evCi.heap_extends),
          hpr, husedNil, by rw [← hownEq]; exact hmem rfl, cb, hcb, hcaM⟩
      match sg with
      | .Defn_Definition_Safe (hv81 := hv) (ev210 := evRun) ..
      | .Defn_Theorem (hv81 := hv) (ev321 := evRun) .. =>
        refine ⟨evRun.heap_extends, Or.inl ?_⟩
        cases hinfo : ca.info with
        | defn d =>
          exact ⟨d, rfl, Decl.adviceRecord_checked hS hrc ha ev hsub hca (Or.inl ⟨d, hinfo⟩)⟩
        | recr _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | axio _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | quot _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | dPrj _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | iPrj _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | cPrj _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | rPrj _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | muts _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
      | .Defn_Definition_other (heq258 := h01) .. | .Defn_Opaque (heq372 := h01) .. =>
        exact absurd (Value.field.inj h01) zero_ne_one
      | .Recr (hv403 := hv) (ev553 := e1) (ev540 := e2) (ev574 := evRun) .. =>
        refine ⟨e1.heap_extends.trans (e2.heap_extends.trans evRun.heap_extends), Or.inr (Or.inl ?_)⟩
        cases hinfo : ca.info with
        | recr rc =>
          exact ⟨rc, rfl,
            Decl.adviceRecord_checked hS hrc ha ev hsub hca (Or.inr (Or.inl ⟨rc, hinfo⟩))⟩
        | defn _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | axio _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | quot _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | dPrj _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | iPrj _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | cPrj _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | rPrj _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | muts _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
      | .Muts (x_members := x_members) (hv598 := hv) (ev629 := evIc) (ev649 := evLen)
          (heq658 := heqLen) (ev683 := evBm) (ev723 := evSafeM) (ev744 := evAll) .. =>
        refine ⟨evIc.heap_extends.trans (evLen.heap_extends.trans (evBm.heap_extends.trans
          (evSafeM.heap_extends.trans evAll.heap_extends))), Or.inr (Or.inr (Or.inl ?_))⟩
        cases hinfo : ca.info with
        | muts ms =>
          obtain ⟨hchkAll, hnat⟩ := Decl.adviceBlock_checked hS hrc ha ev hsub hca hinfo
          -- Also every member is `.indc` from `muts_indc_count = length`
          obtain ⟨extL1, bytesL1, ca', hszL1, hhL1, hblL1, hdeEL1, -, -, -, -, -, -, cRepL1⟩ :=
            L1.load_verified_constant_decode_bounded haOrd evLd
          have eca' : ca' = ca := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hca)
            (Core.hashed_mono hsub12 hhL1) hblL1 hdeEL1
          subst ca'
          obtain ⟨iv', _, _, _, _, hmk', hinfoL1, -, -, -, -⟩ := cRepL1
          injection hmk' with _ _ hargs'; simp only [List.cons.injEq] at hargs'
          obtain ⟨rfl, -⟩ := hargs'
          rw [hinfo] at hinfoL1
          obtain ⟨msPtr, hmsV, hmsList⟩ := hinfoL1
          rw [hv] at hmsV
          injection hmsV with _ _ haM; simp only [List.cons.injEq] at haM
          obtain ⟨rfl, -⟩ := haM
          have hmsSmall : ms.size < 8589934592 := by
            have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound
              ⟨bytesL1.toArray⟩ ca hdeEL1
            have hle : ms.size ≤ ca.resourceSize := Claim.muts_size_le hinfo
            have hblen : (⟨bytesL1.toArray⟩ : ByteArray).size < 4294967296 := by
              simpa [ByteArray.size] using hszL1
            omega
          obtain ⟨hindV, hmIc⟩ := Core.ModeledAux.muts_indc_count_spec
            (Decl.membersRep_of_repMutConstList hmsList) evIc
          rw [← Obs.Names.«Lists::length<Ixon::MutConst>».symbol, hmIc] at evLen
          change RepList Obs.Names.«Lists::Node<Ixon::MutConst>» L1.RepMutConst m2 ms.toList
            x_members at hmsList
          rw [← Obs.Names.«Lists::Node<Ixon::MutConst>».symbol] at hmsList
          obtain ⟨hlenV, -⟩ := Lib.Lists.length_spec evLen hmsList
          have hfeq : ((ms.toList.filter Core.Specs.Callees.isIndc).length : F) =
              (ms.toList.length : F) :=
            Value.field.inj (hindV.symm.trans (heqLen.trans hlenV))
          have hflen : (ms.toList.filter Core.Specs.Callees.isIndc).length = ms.toList.length :=
            Core.ModeledAux.natCast_inj_lt
              (Nat.lt_of_le_of_lt (List.length_filter_le _ _) (Nat.lt_trans (by simpa using hmsSmall) (by decide)))
              (Nat.lt_trans (by simpa using hmsSmall) (by decide)) hfeq
          have hallIndc : ∀ m ∈ ms.toList, ∃ ind, m = .indc ind := by
            intro m hm
            have hbi : Core.Specs.Callees.isIndc m = true :=
              (List.length_filter_eq_length_iff.mp hflen) m hm
            cases m with
            | indc ind => exact ⟨ind, rfl⟩
            | defn _ => simp [Core.Specs.Callees.isIndc, Core.isIndc] at hbi
            | recr _ => simp [Core.Specs.Callees.isIndc, Core.isIndc] at hbi
          exact ⟨ms, rfl, hallIndc, hchkAll, hnat⟩
        | defn _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | recr _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | axio _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | quot _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | dPrj _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | iPrj _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | cPrj _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
        | rPrj _ => rw [hinfo] at hinfoRep; obtain ⟨_, h', -⟩ := hinfoRep; rw [hv] at h'; simp at h'
      | .IPrj (cs_sopfkvlz := csCi) (ev836 := evPb) (ev822 := evMem) (heq858 := h1)
          (ev_gjbqzffr := evCi) (he862 := hh) (hc863 := hcsS) .. =>
        rw [h1] at evMem
        obtain ⟨extS, hpr⟩ := hprojCase hrepC evPb evMem evCi
          (fun cl hcl => hsubSg cl (by rw [hcsS]; simp [hcl]))
        exact ⟨by rw [hh]; exact extS, Or.inr (Or.inr (Or.inr hpr))⟩
      | .CPrj (cs_xamhzxrj := csCi) (ev915 := evPb) (ev901 := evMem) (heq937 := h1)
          (ev_wwojrrlm := evCi) (he941 := hh) (hc942 := hcsS) .. =>
        rw [h1] at evMem
        obtain ⟨extS, hpr⟩ := hprojCase hrepC evPb evMem evCi
          (fun cl hcl => hsubSg cl (by rw [hcsS]; simp [hcl]))
        exact ⟨by rw [hh]; exact extS, Or.inr (Or.inr (Or.inr hpr))⟩
    obtain ⟨extSg, hkind⟩ := hkindSpec
    obtain ⟨extI1, hidxs1⟩ := Claim.const_idxs_of_spec (Claim.RepConstant.mono extSg hrepC) evIdxs1
    have extRefs0 : Heap.Extends h _ := ext2.trans (extSg.trans extI1)
    have hrefsOk := advice_refs_ok_spec hS hH hca hasmall ca.refs.toList 0 (by simp)
      (RepLinkedList.mono Claim.repAddrElem_heapMono₂ (extSg.trans extI1) hrefsRep)
      hidxs1 (haset.mono extRefs0) (hwset.mono extRefs0) (by simpa using evRefs) hsubRefs
    obtain ⟨extI2, hidxs2⟩ := Claim.const_idxs_of_spec
      (Claim.RepConstant.mono (extSg.trans (extI1.trans evRefs.heap_extends)) hrepC) evIdxs2
    have hsafe := assert_inner_refs_safe_spec hS hasmall
      (hrc.mono (extRefs0.trans (evRefs.heap_extends.trans extI2)))
      (RepLinkedList.mono Claim.repAddrElem_heapMono₂
        (extSg.trans (extI1.trans (evRefs.heap_extends.trans extI2))) hrefsRep)
      hidxs2 evSafe hsubSafe
    refine ⟨hordA, ca, hca, hcaLog, hkind, fun ref ⟨ca', j, hca', hj, href⟩ => ?_⟩
    have ec : ca' = ca := Option.some.inj (hca'.symm.trans hca)
    subst ca'
    obtain ⟨-, hcovSafe, hnb, hord⟩ := hsafe j hj ref href
    exact ⟨hnb, hord, hcovSafe, hrefsOk j (Nat.zero_le j) hj ref href⟩

private theorem check_advice_records_indexed_go {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {W : List _root_.Address} :
    ∀ (advAs : List Bytes.Address) (S : List _root_.Address)
      {x_rc x_adv x_seen x_wset r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      Claim.RCLimRep t bAddr lim h x_rc →
      RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h advAs x_adv →
      Claim.RepAddrSet h S x_seen →
      Claim.RepAddrSet h W x_wset →
      ObsFn Obs.W "KernelModeled::check_advice_records" [x_rc, x_adv, x_seen, x_wset] h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∀ (k : Nat) (hk : k < advAs.length),
        AdviceRecordFacts calls bAddr t E₀ lim
          ((advAs.take k).map Core.ixAddr ++ S) W (Core.ixAddr (advAs[k]'hk))
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    intro k hk; simp at hk
  | a :: rest, S, x_rc, x_adv, x_seen, x_wset, r, h, h', cs,
      hrc, hadv, hseen, hwset, ev, hsub => by
    match Obs.«KernelModeled::check_advice_records».obs ev with
    | .Nil (ld12 := ld) .. => exact absurd (Lib.rep_nil_of_load hadv ld) (by simp)
    | .Cons (cs100 := csRec1) (cs138 := csRest) (ld12 := ld)
        (ev_mfihupbr := evSeen) (ev_xzbngsxs := evWset) (ev102 := evCar)
        (ev170 := evIns) (ev140 := evRest) (hc201 := hcs) .. =>
      obtain ⟨a', rest', he, haRep, hrestRep⟩ := Lib.rep_cons_of_load hadv ld
      injection he with ha' hrest'
      subst ha' hrest'
      have hsub1 : ∀ cl ∈ csRec1, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hsubR : ∀ cl ∈ csRest, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have ext1 := evSeen.heap_extends.trans evWset.heap_extends
      have hfacts0 := check_advice_record_spec hS hH (hrc.mono ext1)
        (Bytes.repAddressRef_heapMono₂ Core.addrTy ext1 haRep)
        (hseen.mono ext1) (hwset.mono ext1) evCar hsub1
      have ext2 := ext1.trans evCar.heap_extends
      rw [← Obs.Names.«RBTreeMap::rbtree_map_insert<Field>».symbol] at evIns
      obtain ⟨extIns, hseen1⟩ := Claim.rbtree_set_insert_spec
        (Bytes.repAddressRef_heapMono₂ Core.addrTy ext2 haRep) (hseen.mono ext2) evIns
      have extAll := ext2.trans extIns
      have hfactsRest := check_advice_records_indexed_go hS hH rest (Core.ixAddr a :: S)
        (hrc.mono extAll)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) extAll hrestRep)
        hseen1 (hwset.mono extAll) evRest hsubR
      intro k hk
      cases k with
      | zero =>
        simpa using hfacts0
      | succ k' =>
        have hk' : k' < rest.length := by simpa using hk
        have hstep := hfactsRest k' hk'
        -- `(rest.take k').map ixAddr ++ (ixAddr a :: S)` has the exact same elements as
        -- `((a :: rest).take (k' + 1)).map ixAddr ++ S`
        have hperm : ∀ x, x ∈ (rest.take k').map Core.ixAddr ++ (Core.ixAddr a :: S) →
            x ∈ ((a :: rest).take (k' + 1)).map Core.ixAddr ++ S := by
          intro x hx
          simp only [List.take_succ_cons, List.map_cons, List.cons_append, List.mem_cons,
            List.mem_append] at hx ⊢
          rcases hx with h1 | (rfl | h2)
          · exact Or.inr (Or.inl h1)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr h2)
        obtain ⟨hord, ca, hca, hlog, hkind, hrefs⟩ := hstep
        refine ⟨hord, ca, hca, hlog, ?_, fun ref hu => ?_⟩
        · rcases hkind with h1 | h2 | h3 | ⟨hpr, hnil, hmemS, hcb⟩
          · exact Or.inl h1
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr (Or.inl h3))
          · exact Or.inr (Or.inr (Or.inr ⟨hpr, hnil, hperm _ hmemS, hcb⟩))
        · obtain ⟨hnb, hordR, hcovS, hcls⟩ := hrefs ref hu
          refine ⟨hnb, hordR, hcovS, ?_⟩
          rcases hcls with h1 | h2 | ⟨blk, c, cb, hmemS, hrest⟩
          · exact Or.inl (hperm _ h1)
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr ⟨blk, c, cb, hperm _ hmemS, hrest⟩)

/-- **`KernelModeled::check_advice_records`** starting from the empty set gives indexed
`AdviceRecordFacts` where the seen set at position `k` is `(advAs.take k).map Core.ixAddr`. -/
theorem check_advice_records_indexed_spec {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {advAs : List Bytes.Address} {W : List _root_.Address}
    {x_rc x_adv x_wset r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrc : Claim.RCLimRep t bAddr lim h x_rc)
    (hadv : RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h advAs x_adv)
    (hwset : Claim.RepAddrSet h W x_wset)
    (ev : ObsFn Obs.W "KernelModeled::check_advice_records"
      [x_rc, x_adv, .construct Core.addrMapEnum "Nil" [], x_wset] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∀ (k : Nat) (hk : k < advAs.length),
      AdviceRecordFacts calls bAddr t E₀ lim
        ((advAs.take k).map Core.ixAddr) W (Core.ixAddr (advAs[k]'hk)) := by
  intro k hk
  have h1 := check_advice_records_indexed_go hS hH advAs [] hrc hadv
    (Claim.RepAddrSet.nil h) hwset ev hsub k hk
  simpa using h1

/-! ## `container_recs_refs` and `container_refs_check` specification -/

private theorem container_refs_ok_spec {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {self ib : _root_.Address} {cown cib : Ixon.Constant} {W : List _root_.Address}
    (hcib : recordOf E₀ ib = some cib) (hIbsmall : cib.refs.size < 8589934592)
    (hownSmall : cown.refs.size < 8589934592) :
    ∀ (xs : List _root_.Address) (i : Nat)
      {x_rc x_refs x_used x_self x_ib x_irefs x_iused x_wset r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      cown.refs.toList.drop i = xs →
      RepList Core.addrListEnum Claim.RepAddrElem h xs x_refs →
      RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h (Core.S0.usedRefIdxs cown) x_used →
      Core.S0.addr h x_self self →
      Core.S0.addr h x_ib ib →
      RepList Core.addrListEnum Claim.RepAddrElem h cib.refs.toList x_irefs →
      RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h (Core.S0.usedRefIdxs cib) x_iused →
      Claim.RepAddrSet h W x_wset →
      ObsFn Obs.W "KernelModeled::container_refs_ok"
        [x_rc, x_refs, x_used, .field (i : F), x_self, x_ib, x_irefs, x_iused, x_wset] h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∀ j, i ≤ j → j ∈ usedRefIdxs cown → ∀ ref, cown.refs[j]? = some ref →
        ref ≠ self ∧
        (UsedRef E₀ ib ref ∨
          (∃ c cb, recordOf E₀ ref = some c ∧ IsProj c ∧ Ix.Cert.ownerOf ref c = ib ∧
            usedRefIdxs c = [] ∧ recordOf E₀ ib = some cb ∧ ConstAddrOf ib cb ref) ∨
          (∃ blk c cb, PathPos E₀ ib blk ∧ recordOf E₀ ref = some c ∧ IsProj c ∧
            Ix.Cert.ownerOf ref c = blk ∧ usedRefIdxs c = [] ∧
            recordOf E₀ blk = some cb ∧ ConstAddrOf blk cb ref) ∨
          (ref ∈ W ∧ ∃ cr, recordOf E₀ ref = some cr ∧
            (∀ rc, cr.info ≠ .recr rc) ∧ (∀ rp, cr.info ≠ .rPrj rp)))
  | [], i, _, _, _, _, _, _, _, _, _, _, _, _, hdrop, _, _, _, _, _, _, _, _, _ => by
    intro j hij _ ref href
    have hge : cown.refs.toList.length ≤ i := List.drop_eq_nil_iff.mp hdrop
    rw [← Array.getElem?_toList] at href
    have hlt := (List.getElem?_eq_some_iff.mp href).1
    omega
  | r0 :: rest, i, x_rc, x_refs, x_used, x_self, x_ib, x_irefs, x_iused, x_wset, r, h, h', cs,
      hdrop, hrefs, hused, hself, hib, hirefs, hiused, hwset, ev, hsub => by
    have hiLt : i < cown.refs.size := by
      have hne : cown.refs.toList.drop i ≠ [] := by rw [hdrop]; simp
      have : i < cown.refs.toList.length := by
        by_contra hge; exact hne (List.drop_eq_nil_iff.mpr (by omega))
      simpa using this
    have hiBound : i < 72057594037927936 := by omega
    match Obs.«KernelModeled::container_refs_ok».obs ev with
    | .Nil (ld12 := ld) .. => exact absurd (Lib.rep_nil_of_load hrefs ld) (by simp)
    | .Cons (x_r := x_r) (m385 := m385) (cs387 := csSg) (cs396 := csRec)
        (ld12 := ld) (sg392 := sg) (op_gskedpnl := opAdd) (ev398 := evRec) (hc463 := hcs) .. =>
      obtain ⟨r0', rest', he, hr0Addr, hrestRep⟩ := Lib.rep_cons_of_load hrefs ld
      injection he with hr0' hrest'
      subst hr0' hrest'
      have hsubSg : ∀ cl ∈ csSg, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hsubRec : ∀ cl ∈ csRec, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hneSelf : ∀ {m43 m_eq : Heap F} {v_eq : SourceValue F} {cs_eq : List (Call F)},
          Heap.Extends h m43 →
          ObsFn Obs.W "Bytes::address_eq" [x_r, x_self] m43 v_eq m_eq cs_eq →
          v_eq = .field 0 → r0 ≠ self := by
        intro m43 m_eq v_eq cs_eq ext43 evEq hv0 heq
        obtain ⟨br, hbr, rfl⟩ := hr0Addr
        obtain ⟨bs, hbs, rfl⟩ := hself
        have ebs : br = bs := by
          have := congrArg (fun a : _root_.Address => a.hash.data.toList) heq
          simpa [Core.ixAddr] using this
        subst ebs
        obtain ⟨hrEq, -⟩ := Lib.address_eq_spec evEq
          (Bytes.repAddressRef_heapMono₂ Core.addrTy ext43 hbr)
          (Bytes.repAddressRef_heapMono₂ Core.addrTy ext43 hbs)
        simp only [↓reduceIte] at hrEq
        exact zero_ne_one (Value.field.inj (hv0.symm.trans hrEq))
      have hr0Spec : Heap.Extends h m385 ∧
          (i ∈ usedRefIdxs cown →
            r0 ≠ self ∧
            (UsedRef E₀ ib r0 ∨
              (∃ c cb, recordOf E₀ r0 = some c ∧ IsProj c ∧ Ix.Cert.ownerOf r0 c = ib ∧
                usedRefIdxs c = [] ∧ recordOf E₀ ib = some cb ∧ ConstAddrOf ib cb r0) ∨
              (∃ blk c cb, PathPos E₀ ib blk ∧ recordOf E₀ r0 = some c ∧ IsProj c ∧
                Ix.Cert.ownerOf r0 c = blk ∧ usedRefIdxs c = [] ∧
                recordOf E₀ blk = some cb ∧ ConstAddrOf blk cb r0) ∨
              (r0 ∈ W ∧ ∃ cr, recordOf E₀ r0 = some cr ∧
                (∀ rc, cr.info ≠ .recr rc) ∧ (∀ rp, cr.info ≠ .rPrj rp)))) := by
        match sg with
        | .n1_n1 (ev56 := e1) (ev_tojkhkzc := evEq) (heq_fltizyxe := h0)
            (ev99 := evUrh) (he165 := hh) .. =>
          have ext2 := e1.heap_extends.trans evEq.heap_extends
          refine ⟨by rw [hh]; exact ext2.trans evUrh.heap_extends, fun _ =>
            ⟨hneSelf e1.heap_extends evEq h0, Or.inl (used_ref_has_spec hcib hIbsmall
              cib.refs.toList 0 (by simp)
              (RepLinkedList.mono Claim.repAddrElem_heapMono₂ ext2 hirefs)
              (RepLinkedList.mono (fun _ _ _ _ _ r => r) ext2 hiused)
              (Core.S0.addr_mono ext2 hr0Addr) (by simpa using evUrh))⟩⟩
        | .n1_other_n1 (cs183 := csIp) (ev56 := e1) (ev_tojkhkzc := evEq) (heq_fltizyxe := h0)
            (ev99 := e2) (ev185 := evIp) (he236 := hh) (hc237 := hcsS) .. =>
          have ext3 := e1.heap_extends.trans (evEq.heap_extends.trans e2.heap_extends)
          refine ⟨by rw [hh]; exact ext3.trans evIp.heap_extends, fun _ =>
            ⟨hneSelf e1.heap_extends evEq h0, Or.inr (Or.inl (is_projection_of_spec hS hH
              (Core.S0.addr_mono ext3 hr0Addr) (Core.S0.addr_mono ext3 hib) evIp
              (fun cl hcl => hsubSg cl (by rw [hcsS]; simp [hcl]))))⟩⟩
        | .n1_other_other_n1 (cs254 := csPrb) (ev56 := e1) (ev_tojkhkzc := evEq)
            (heq_fltizyxe := h0) (ev99 := e2) (ev185 := e3) (ev256 := evPrb)
            (he315 := hh) (hc316 := hcsS) .. =>
          have ext4 := e1.heap_extends.trans (evEq.heap_extends.trans
            (e2.heap_extends.trans e3.heap_extends))
          refine ⟨by rw [hh]; exact ext4.trans evPrb.heap_extends, fun _ =>
            ⟨hneSelf e1.heap_extends evEq h0, Or.inr (Or.inr (Or.inl
              (projection_of_ref_block_spec hS hH hcib hIbsmall
                (Core.S0.addr_mono ext4 hr0Addr)
                (RepLinkedList.mono Claim.repAddrElem_heapMono₂ ext4 hirefs)
                (RepLinkedList.mono (fun _ _ _ _ _ r => r) ext4 hiused)
                evPrb (fun cl hcl => hsubSg cl (by rw [hcsS]; simp [hcl])))))⟩⟩
        | .n1_other_other_other_n1_Recr (heq_jwmirhum := h01) ..
        | .n1_other_other_other_n1_RPrj (heq_rbmskoff := h01) ..
        | .n1_other_other_other_other (heq_siovpfty := h01) .. =>
          exact absurd (Value.field.inj h01) zero_ne_one
        | .n1_other_other_other_n1_other (cs_nlmkvjrk := csLd)
            (ev56 := e1) (ev_tojkhkzc := evEq) (heq_fltizyxe := h0)
            (ev99 := e2) (ev185 := e3) (ev256 := e4) (ev_ntfvqzva := evMem)
            (ev_eauaaxrq := evLd) (hne_qzgodjon := hneRecr) (hne_vgdvhltn := hneRprj)
            (he_nqrzigtc := hh) (hc_xkxroafj := hcsS) .. =>
          have ext5 := e1.heap_extends.trans (evEq.heap_extends.trans
            (e2.heap_extends.trans (e3.heap_extends.trans e4.heap_extends)))
          have ext6 := ext5.trans evMem.heap_extends
          refine ⟨by rw [hh]; exact ext6.trans evLd.heap_extends, fun _ => ?_⟩
          obtain ⟨br, hbr, rfl⟩ := hr0Addr
          obtain ⟨hm, -⟩ := Claim.addr_set_member_set_spec
            (Bytes.repAddressRef_heapMono₂ Core.addrTy ext5 hbr) (hwset.mono ext5) evMem
          obtain ⟨-, raw, cr, hszR, hhR, hblR, hdeR, hdeER, hrepR, -⟩ :=
            Claim.load_verified_constant_de
              ⟨br, Bytes.repAddressRef_heapMono₂ Core.addrTy ext6 hbr, rfl⟩ evLd
          have hsubLd : ∀ cl ∈ csLd, cl ∈ calls := fun cl hcl =>
            hsubSg cl (by rw [hcsS]; simp [hcl])
          have hcr : recordOf E₀ (Core.ixAddr br) = some cr := by
            rw [← hblR]
            exact Claim.recordOf_hashed hS hH (Core.hashed_mono hsubLd hhR) hszR hdeR hdeER
          obtain ⟨iv, _, _, _, _, hmk, hinfoR, -⟩ := hrepR
          injection hmk with _ _ haR; simp only [List.cons.injEq] at haR
          obtain ⟨rfl, -⟩ := haR
          refine ⟨hneSelf e1.heap_extends evEq h0, Or.inr (Or.inr (Or.inr ⟨hm rfl, cr, hcr, ?_, ?_⟩))⟩
          · intro rc hrc
            rw [hrc] at hinfoR
            obtain ⟨rv, hv, -⟩ := hinfoR
            exact hneRecr [rv] rfl hv
          · intro rp hrp
            rw [hrp] at hinfoR
            obtain ⟨rv, hv, -⟩ := hinfoR
            exact hneRprj [rv] rfl hv
        | .other (ev56 := evHas) (hne375 := hne1) (he382 := hh) .. =>
          refine ⟨by rw [hh]; exact evHas.heap_extends, fun hi => ?_⟩
          have h1 := (Claim.g_list_has_spec (Core.S0.usedRefIdxs cown) hiBound hused evHas).2.mpr
            (by rwa [Assembly.usedRefIdxs_eq])
          exact (hne1 h1).elim
      obtain ⟨extSg, hr0Cls⟩ := hr0Spec
      simp only [evalBinOp, Except.ok.injEq] at opAdd
      subst opAdd
      have hcast : ((i : F) + 1) = ((i + 1 : Nat) : F) := by push_cast; rfl
      rw [hcast] at evRec
      have hdrop1 : cown.refs.toList.drop (i + 1) = rest := by
        have h1 : (cown.refs.toList.drop i).tail = cown.refs.toList.drop (i + 1) := by
          rw [List.tail_drop]
        rw [← h1, hdrop]; rfl
      have hrecCls := container_refs_ok_spec hS hH hcib hIbsmall hownSmall rest (i + 1) hdrop1
        (RepLinkedList.mono Claim.repAddrElem_heapMono₂ extSg hrestRep)
        (RepLinkedList.mono (fun _ _ _ _ _ r => r) extSg hused)
        (Core.S0.addr_mono extSg hself) (Core.S0.addr_mono extSg hib)
        (RepLinkedList.mono Claim.repAddrElem_heapMono₂ extSg hirefs)
        (RepLinkedList.mono (fun _ _ _ _ _ r => r) extSg hiused)
        (hwset.mono extSg) evRec hsubRec
      intro j hij hj ref href
      by_cases hji : j = i
      · subst hji
        have heq : ref = r0 := by
          rw [← Array.getElem?_toList, ← List.head?_drop, hdrop] at href
          exact (Option.some.inj href).symm
        subst heq
        exact hr0Cls hj
      · exact hrecCls j (by omega) hj ref href

/-- **Facts proved by `KernelModeled::container_refs_check`** on a container recursor `x`
(whose owning record is `own = Ix.Cert.ownerOf x cx`) relative to its `rec_family_block` `ib`
and witness set `W`. -/
def ContainerRefsFacts (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (lim : Option Nat)
    (W : List _root_.Address) (x : _root_.Address) : Prop :=
  ∀ cx, recordOf E₀ x = some cx →
    ((∃ rc, cx.info = .recr rc) ∨ (∃ rp, cx.info = .rPrj rp)) →
    ∃ ib,
      (∃ (h₁ h₂ : Heap F) (xx' r' : SourceValue F) (cs' : List (Call F)) (b_ib : Bytes.Address),
        Core.S0.addr h₁ xx' x ∧
        ObsFn Obs.W "KernelModeled::rec_family_block" [xx'] h₁ r' h₂ cs' ∧
        Bytes.RepAddressRef Core.addrTy h₂ b_ib r' ∧ Core.ixAddr b_ib = ib ∧
        ∀ cl ∈ cs', cl ∈ calls) ∧
      ∀ ref, UsedRef E₀ (Ix.Cert.ownerOf x cx) ref →
        ref ≠ x ∧
        Claim.NotBlockIn calls ref ∧ Claim.OpOrderedAt t lim ref ∧
        (¬ Claim.CoveredAt t lim ref → Claim.SourceSafe E₀ ref) ∧
        (UsedRef E₀ ib ref ∨
          (∃ c cb, recordOf E₀ ref = some c ∧ IsProj c ∧ Ix.Cert.ownerOf ref c = ib ∧
            usedRefIdxs c = [] ∧ recordOf E₀ ib = some cb ∧ ConstAddrOf ib cb ref) ∨
          (∃ blk c cb, PathPos E₀ ib blk ∧ recordOf E₀ ref = some c ∧ IsProj c ∧
            Ix.Cert.ownerOf ref c = blk ∧ usedRefIdxs c = [] ∧
            recordOf E₀ blk = some cb ∧ ConstAddrOf blk cb ref) ∨
          (ref ∈ W ∧ ∃ cr, recordOf E₀ ref = some cr ∧
            (∀ rc, cr.info ≠ .recr rc) ∧ (∀ rp, cr.info ≠ .rPrj rp)))

private theorem container_refs_check_spec {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat}
    (hC : CollisionFreeRun calls E₀) (hbd : IxVM.Consistency.Bounded calls)
    {x own : _root_.Address} {cown : Ixon.Constant} {W : List _root_.Address}
    {x_rc x_x x_c x_wset r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrc : Claim.RCLimRep t bAddr lim h x_rc)
    (hx : Core.S0.addr h x_x x)
    (hcown : recordOf E₀ own = some cown) (hownSmall : cown.refs.size < 8589934592)
    (hrepOwn : Claim.RepConstant h cown x_c)
    (hwset : Claim.RepAddrSet h W x_wset)
    (ev : ObsFn Obs.W "KernelModeled::container_refs_check" [x_rc, x_x, x_c, x_wset] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∃ ib,
      (∃ (h₁ h₂ : Heap F) (xx' r' : SourceValue F) (cs' : List (Call F)) (b_ib : Bytes.Address),
        Core.S0.addr h₁ xx' x ∧
        ObsFn Obs.W "KernelModeled::rec_family_block" [xx'] h₁ r' h₂ cs' ∧
        Bytes.RepAddressRef Core.addrTy h₂ b_ib r' ∧ Core.ixAddr b_ib = ib ∧
        ∀ cl ∈ cs', cl ∈ calls) ∧
      ∀ ref, UsedRef E₀ own ref →
        ref ≠ x ∧
        Claim.NotBlockIn calls ref ∧ Claim.OpOrderedAt t lim ref ∧
        (¬ Claim.CoveredAt t lim ref → Claim.SourceSafe E₀ ref) ∧
        (UsedRef E₀ ib ref ∨
          (∃ c cb, recordOf E₀ ref = some c ∧ IsProj c ∧ Ix.Cert.ownerOf ref c = ib ∧
            usedRefIdxs c = [] ∧ recordOf E₀ ib = some cb ∧ ConstAddrOf ib cb ref) ∨
          (∃ blk c cb, PathPos E₀ ib blk ∧ recordOf E₀ ref = some c ∧ IsProj c ∧
            Ix.Cert.ownerOf ref c = blk ∧ usedRefIdxs c = [] ∧
            recordOf E₀ blk = some cb ∧ ConstAddrOf blk cb ref) ∨
          (ref ∈ W ∧ ∃ cr, recordOf E₀ ref = some cr ∧
            (∀ rc, cr.info ≠ .recr rc) ∧ (∀ rp, cr.info ≠ .rPrj rp))) := by
  match Obs.«KernelModeled::container_refs_check».obs ev with
  | .run (cs12 := csRfb) (cs34 := csIb) (x_refs := x_refs) (x_irefs := x_irefs)
      (cs_pwnfsnzi := csOk) (cs_zlhtmzlz := csSafe)
      (ev14 := evRfb) (ev36 := evIb) (hv59 := hvOwn)
      (ev_iroawuwo := evIdxsOwn) (ev_yqrkylod := evIdxsIb)
      (ev_wymffvuv := evOk) (ev_ozxzdina := evIdxsOwn2) (ev_tnqzszcy := evSafe)
      (hc222 := hcs) .. =>
    have hsubRfb : ∀ cl ∈ csRfb, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsubIb : ∀ cl ∈ csIb, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsubOk : ∀ cl ∈ csOk, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsubSafe : ∀ cl ∈ csSafe, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    obtain ⟨bx, hbx, rfl⟩ := hx
    obtain ⟨_, _, _, _, ib, bib, _, _, -, -, -, -, hbibEq, hbibRep, -⟩ :=
      rec_family_block_head_spec hC hbd ⟨bx, hbx, rfl⟩ evRfb hsubRfb
    obtain ⟨extIb, rawIb, cib, hszIb, hhIb, hblIb, hdeIb, hdeEIb, hrepIb, -⟩ :=
      Claim.load_verified_constant_de ⟨bib, hbibRep, rfl⟩ evIb
    have hcib : recordOf E₀ (Core.ixAddr bib) = some cib := by
      rw [← hblIb]
      exact Claim.recordOf_hashed hC.runStore hC.hashedStored (Core.hashed_mono hsubIb hhIb)
        hszIb hdeIb hdeEIb
    have hIbsmall := refs_small_of_decoded hszIb hdeEIb
    have ext24 : Heap.Extends h _ := evRfb.heap_extends.trans extIb
    have hrepOwn24 := Claim.RepConstant.mono ext24 hrepOwn
    obtain ⟨extI1, hidxsOwn⟩ := Claim.const_idxs_of_spec hrepOwn24 evIdxsOwn
    obtain ⟨extI2, hidxsIb⟩ := Claim.const_idxs_of_spec (Claim.RepConstant.mono extI1 hrepIb) evIdxsIb
    obtain ⟨_, _, rpOwn, _, _, hmkOwn, _, _, hrefsOwn, _, _⟩ := id hrepOwn24
    rw [hvOwn] at hmkOwn
    injection hmkOwn with _ _ haOwn; simp only [List.cons.injEq] at haOwn
    obtain ⟨-, -, rfl, -⟩ := haOwn
    obtain ⟨_, _, rpIb, _, _, hmkIb, -, -, hrefsIb, -, -⟩ := hrepIb
    injection hmkIb with _ _ haIb; simp only [List.cons.injEq] at haIb
    obtain ⟨-, -, rfl, -⟩ := haIb
    have extOk0 : Heap.Extends h _ := ext24.trans (extI1.trans extI2)
    have hok := container_refs_ok_spec hC.runStore hC.hashedStored hcib hIbsmall hownSmall
      cown.refs.toList 0 (by simp)
      (RepLinkedList.mono Claim.repAddrElem_heapMono₂ (extI1.trans extI2) hrefsOwn)
      (RepLinkedList.mono (fun _ _ _ _ _ r => r) extI2 hidxsOwn)
      (Core.S0.addr_mono extOk0 ⟨bx, hbx, rfl⟩)
      ⟨bib, Bytes.repAddressRef_heapMono₂ Core.addrTy (extIb.trans (extI1.trans extI2)) hbibRep, rfl⟩
      (RepLinkedList.mono Claim.repAddrElem_heapMono₂ (extI1.trans extI2) hrefsIb)
      hidxsIb (hwset.mono extOk0) (by simpa using evOk) hsubOk
    have extOk1 : Heap.Extends _ _ := (extI1.trans extI2).trans evOk.heap_extends
    obtain ⟨extI3, hidxsOwn2⟩ := Claim.const_idxs_of_spec
      (Claim.RepConstant.mono extOk1 hrepOwn24) evIdxsOwn2
    have hsafe := assert_inner_refs_safe_spec hC.runStore hownSmall
      (hrc.mono (extOk0.trans (evOk.heap_extends.trans extI3)))
      (RepLinkedList.mono Claim.repAddrElem_heapMono₂ (extOk1.trans extI3) hrefsOwn)
      hidxsOwn2 evSafe hsubSafe
    refine ⟨Core.ixAddr bib, ⟨_, _, _, _, csRfb, bib, ⟨bx, hbx, rfl⟩, evRfb, hbibRep, rfl, hsubRfb⟩,
      fun ref ⟨cown', j, hcown', hj, href⟩ => ?_⟩
    have ec : cown' = cown := Option.some.inj (hcown'.symm.trans hcown)
    subst cown'
    obtain ⟨-, hcovSafe, hnb, hord⟩ := hsafe j hj ref href
    obtain ⟨hne, hcls⟩ := hok j (Nat.zero_le j) hj ref href
    exact ⟨hne, hnb, hord, hcovSafe, hcls⟩

/-- **`KernelModeled::container_recs_refs`**: for every witness `b ∈ outs`, gives
`ContainerRefsFacts` (covering both standalone `Recr` and block-projected `RPrj`). -/
theorem container_recs_refs_spec {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat}
    (hC : CollisionFreeRun calls E₀) (hbd : IxVM.Consistency.Bounded calls)
    {W : List _root_.Address} :
    ∀ (outs : List Bytes.Address) {x_rc x_xs x_wset r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      Claim.RCLimRep t bAddr lim h x_rc →
      RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h outs x_xs →
      Claim.RepAddrSet h W x_wset →
      ObsFn Obs.W "KernelModeled::container_recs_refs" [x_rc, x_xs, x_wset] h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∀ b ∈ outs, ContainerRefsFacts calls bAddr t E₀ lim W (Core.ixAddr b)
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => by
    intro b hb; cases hb
  | a :: rest, x_rc, x_xs, x_wset, r, h, h', cs, hrc, houts, hwset, ev, hsub => by
    match Obs.«KernelModeled::container_recs_refs».obs ev with
    | .Nil (ld12 := ld) .. => exact absurd (Lib.rep_nil_of_load houts ld) (by simp)
    | .Cons_Recr (cs53 := csLd) (cs142 := csChk) (cs172 := csRest) (ld12 := ld)
        (ev55 := evLd) (ev144 := evChk) (ev174 := evRest) (hc191 := hcs) .. =>
      obtain ⟨a', rest', he, haRep, hrestRep⟩ := Lib.rep_cons_of_load houts ld
      injection he with ha' hrest'
      subst ha' hrest'
      have hsubLd : ∀ cl ∈ csLd, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hsubChk : ∀ cl ∈ csChk, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hsubRest : ∀ cl ∈ csRest, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      obtain ⟨extLd, raw, ca, hsz, hh, hbl, hde, hdeE, hrepC, -⟩ :=
        Claim.load_verified_constant_de ⟨a, haRep, rfl⟩ evLd
      have hca : recordOf E₀ (Core.ixAddr a) = some ca := by
        rw [← hbl]
        exact Claim.recordOf_hashed hC.runStore hC.hashedStored (Core.hashed_mono hsubLd hh)
          hsz hde hdeE
      have hasmall := refs_small_of_decoded hsz hdeE
      have hchk := container_refs_check_spec hC hbd (hrc.mono extLd)
        ⟨a, Bytes.repAddressRef_heapMono₂ Core.addrTy extLd haRep, rfl⟩
        hca hasmall hrepC (hwset.mono extLd) evChk hsubChk
      have extRest := extLd.trans evChk.heap_extends
      have hrest := container_recs_refs_spec hC hbd rest (hrc.mono extRest)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) extRest hrestRep)
        (hwset.mono extRest) evRest hsubRest
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · intro cx hcx hkind
        have ec : cx = ca := Option.some.inj (hcx.symm.trans hca)
        subst ec
        -- `ca.info` is `.recr`, so `ownerOf (ixAddr a) ca = ixAddr a`
        obtain ⟨iv, _, _, _, _, hmk, hinfoR, -⟩ := hrepC
        injection hmk with _ _ haM; simp only [List.cons.injEq] at haM
        obtain ⟨rfl, -⟩ := haM
        rcases hkind with ⟨rc, hrc'⟩ | ⟨rp, hrp'⟩
        · simpa [Ix.Cert.ownerOf, hrc'] using hchk
        · rw [hrp'] at hinfoR
          obtain ⟨_, hv, -⟩ := hinfoR; simp at hv
      · exact hrest b hb'
    | .Cons_RPrj (cs53 := csLd) (cs_cywpcyta := csLdB) (cs208 := csChk) (cs264 := csRest)
        (ld12 := ld) (ev55 := evLd) (ev_fvuqobfi := evPb) (ev_vyniyqbz := evLdB)
        (ev210 := evChk) (ev266 := evRest) (hc283 := hcs) .. =>
      obtain ⟨a', rest', he, haRep, hrestRep⟩ := Lib.rep_cons_of_load houts ld
      injection he with ha' hrest'
      subst ha' hrest'
      have hsubLd : ∀ cl ∈ csLd, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hsubLdB : ∀ cl ∈ csLdB, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hsubChk : ∀ cl ∈ csChk, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hsubRest : ∀ cl ∈ csRest, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      obtain ⟨extLd, raw, ca, hsz, hh, hbl, hde, hdeE, hrepC, -⟩ :=
        Claim.load_verified_constant_de ⟨a, haRep, rfl⟩ evLd
      have hca : recordOf E₀ (Core.ixAddr a) = some ca := by
        rw [← hbl]
        exact Claim.recordOf_hashed hC.runStore hC.hashedStored (Core.hashed_mono hsubLd hh)
          hsz hde hdeE
      obtain ⟨-, hpr, b_own, hownRep, hownEq⟩ :=
        projection_block_claim_spec (a := Core.ixAddr a) hrepC evPb
      obtain ⟨extLdB, rawB, cb, hszB, hhB, hblB, hdeB, hdeEB, hrepB, -⟩ :=
        Claim.load_verified_constant_de ⟨b_own, hownRep, rfl⟩ evLdB
      have hcb : recordOf E₀ (Core.ixAddr b_own) = some cb := by
        rw [← hblB]
        exact Claim.recordOf_hashed hC.runStore hC.hashedStored (Core.hashed_mono hsubLdB hhB)
          hszB hdeB hdeEB
      have hbsmall := refs_small_of_decoded hszB hdeEB
      have extChk0 := extLd.trans (evPb.heap_extends.trans extLdB)
      have hchk := container_refs_check_spec hC hbd (hrc.mono extChk0)
        ⟨a, Bytes.repAddressRef_heapMono₂ Core.addrTy extChk0 haRep, rfl⟩
        hcb hbsmall hrepB (hwset.mono extChk0) evChk hsubChk
      have extRest := extChk0.trans evChk.heap_extends
      have hrest := container_recs_refs_spec hC hbd rest (hrc.mono extRest)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) extRest hrestRep)
        (hwset.mono extRest) evRest hsubRest
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · intro cx hcx _
        have ec : cx = ca := Option.some.inj (hcx.symm.trans hca)
        subst ec
        simpa [hownEq] using hchk
      · exact hrest b hb'
    | .Cons_other (cs53 := csLd) (cs293 := csRest) (ld12 := ld)
        (ev55 := evLd) (hne192 := hneRecr) (hne284 := hneRprj)
        (ev295 := evRest) (hc312 := hcs) .. =>
      obtain ⟨a', rest', he, haRep, hrestRep⟩ := Lib.rep_cons_of_load houts ld
      injection he with ha' hrest'
      subst ha' hrest'
      have hsubLd : ∀ cl ∈ csLd, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hsubRest : ∀ cl ∈ csRest, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      obtain ⟨extLd, raw, ca, hsz, hh, hbl, hde, hdeE, hrepC, -⟩ :=
        Claim.load_verified_constant_de ⟨a, haRep, rfl⟩ evLd
      have hca : recordOf E₀ (Core.ixAddr a) = some ca := by
        rw [← hbl]
        exact Claim.recordOf_hashed hC.runStore hC.hashedStored (Core.hashed_mono hsubLd hh)
          hsz hde hdeE
      have hrest := container_recs_refs_spec hC hbd rest (hrc.mono extLd)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) extLd hrestRep)
        (hwset.mono extLd) evRest hsubRest
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · intro cx hcx hkind
        have ec : cx = ca := Option.some.inj (hcx.symm.trans hca)
        subst ec
        obtain ⟨iv, _, _, _, _, hmk, hinfoR, -⟩ := hrepC
        injection hmk with _ _ haM; simp only [List.cons.injEq] at haM
        obtain ⟨rfl, -⟩ := haM
        rcases hkind with ⟨rc, hrc'⟩ | ⟨rp, hrp'⟩
        · rw [hrc'] at hinfoR; obtain ⟨rv, hv, -⟩ := hinfoR
          exact (hneRecr [rv] rfl hv).elim
        · rw [hrp'] at hinfoR; obtain ⟨rv, hv, -⟩ := hinfoR
          exact (hneRprj [rv] rfl hv).elim
      · exact hrest b hb'

/-! ## Master unpack of `FamilyCallOwn` -/

/-- **Complete unpacked witness, advice, container, and family-reference invariants** of an
observed `FamilyCallExact calls bAddr t B rb lim cs advAs` at witness list `outs`. -/
structure FamilyCallUnpacked (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (B rb : _root_.Address) (lim : Option Nat)
    (cs : List (Call F)) (advAs outs : List Bytes.Address) : Prop where
  rbOrdered : Claim.OpOrderedAt t lim rb
  outsOrdered : ∀ w ∈ outs.map Core.ixAddr, Claim.OpOrderedAt t lim w
  outsClassified : ∀ w ∈ outs.map Core.ixAddr,
    (∃ ro : Ix.Kernel.Role, t.addressOf? ro = some w ∧
      Ix.SpecDigest.groupOf ro < 6 ∧
      (RoleVal.roleWalksBound ro = true ∨ RoleVal.isQuotRole ro = true)) ∨
    (PathPos E₀ B w ∧ Claim.NotBlockIn calls w ∧
      ∃ c, recordOf E₀ w = some c ∧
        (IsProj c → usedRefIdxs c = [] ∧
          ∃ cb, recordOf E₀ (Ix.Cert.ownerOf w c) = some cb ∧
            ConstAddrOf (Ix.Cert.ownerOf w c) cb w)) ∨
    (DirectContOwn calls bAddr t B rb lim cs advAs w ∧
      ∃ ib, PathPos E₀ B ib ∧
        ∃ (h₁ h₂ : Heap F) (rc₁ xx₁ xib₁ r₁ : SourceValue F) (cs₁ : List (Call F)),
          Claim.RCLimRep t bAddr lim h₁ rc₁ ∧
          Core.S0.addr h₁ xx₁ w ∧ Core.S0.addr h₁ xib₁ ib ∧
          ObsFn Obs.W "KernelModeled::check_container_rec" [rc₁, xx₁, xib₁] h₁ r₁ h₂ cs₁ ∧
          (∀ cl ∈ cs₁, cl ∈ calls)) ∨
    (∃ ib c cib, PathPos E₀ B ib ∧ recordOf E₀ w = some c ∧ IsProj c ∧
      Ix.Cert.ownerOf w c = ib ∧ usedRefIdxs c = [] ∧
      recordOf E₀ ib = some cib ∧ ConstAddrOf ib cib w)
  contRefs : ∀ w ∈ outs.map Core.ixAddr,
    ContainerRefsFacts calls bAddr t E₀ lim (outs.map Core.ixAddr) w
  adviceFacts : ∀ (k : Nat) (hk : k < advAs.length),
    AdviceRecordFacts calls bAddr t E₀ lim
      ((advAs.take k).map Core.ixAddr) (outs.map Core.ixAddr) (Core.ixAddr (advAs[k]'hk))
  famRefs : ∀ ref, UsedRef E₀ rb ref →
    Claim.NotBlockIn calls ref ∧ Claim.OpOrderedAt t lim ref ∧
    (¬ Claim.CoveredAt t lim ref → Claim.SourceSafe E₀ ref) ∧
    (UsedRef E₀ B ref ∨
      (∃ c cb, recordOf E₀ ref = some c ∧ IsProj c ∧ Ix.Cert.ownerOf ref c = B ∧
        usedRefIdxs c = [] ∧ recordOf E₀ B = some cb ∧ ConstAddrOf B cb ref) ∨
      (∃ blk c cb, PathPos E₀ B blk ∧ recordOf E₀ ref = some c ∧ IsProj c ∧
        Ix.Cert.ownerOf ref c = blk ∧ usedRefIdxs c = [] ∧
        recordOf E₀ blk = some cb ∧ ConstAddrOf blk cb ref) ∨
      ref ∈ outs.map Core.ixAddr)

/-- **Every observed `FamilyCallAtLim` carries its exact own advice list and reference guards
(`FamilyCallExact`).** -/
theorem familyCallExact_of_call {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {B rb : _root_.Address} {lim : Option Nat} {cs : List (Call F)}
    (hfc : FamilyCallAtLim calls bAddr t B rb lim cs) :
    ∃ advAs, FamilyCallExact calls bAddr t B rb lim cs advAs := by
  obtain ⟨h, h', rc, xb, xrb, r, hrc, hxb, hxrb, ev, hmem, hsub⟩ := hfc
  have hpath := Obs.«KernelModeled::check_family».obs ev
  match hpath with
  | .run (m105 := m105) (sg112 := sg112) (ev126 := ev126) (ev148 := ev148) (ev194 := ev194)
      (ev_yqjbwijz := evOrd) (ev231 := ev231) (ev266 := ev266) (ev309 := ev309)
      (ev344 := evWs) (ev403 := evAsb) (ev435 := evCrr) (ev465 := evAdv)
      (ev513 := ev513) (ev601 := ev601) (ev634 := ev634) (ev664 := ev664)
      (ev686 := ev686) (ev716 := ev716) (ev759 := ev759) (ev817 := ev817)
      (ev796 := ev796) (ev852 := ev852) (ev_ursqbimm := evNoRole) (ev874 := ev874)
      (ev896 := ev896) (ev960 := ev960) (ev939 := ev939) (ev1011 := ev1011)
      (ev990 := ev990) (ev_edyzsqzv := evM1) (ev_gkddqxhv := evCat)
      (ev_ittpynob := evM2) (ev_biaifgpd := evM3) (ev1203 := ev1203)
      (ev_cwwgzxtj := evFlat) (ev1246 := ev1246) (ev_mitevvsv := evFlen)
      (ev_rqpeovbn := evZ1) (ev_xrhmaojz := evZ2) (ev_whimdwjd := evVg)
      (ev1305 := evFro) (hc1474 := hc1474) .. =>
    have e0 : Heap.Extends h m105 := by
      match sg112 with
      | .Nil (ev15 := ev15) (he33 := he33) .. => rw [he33]; exact ev15.heap_extends
      | .Node (heq97 := heq) .. => exact absurd (Value.field.inj heq) zero_ne_one
    have ext184 : Heap.Extends h _ :=
      e0.trans (ev126.heap_extends.trans (ev148.heap_extends.trans ev194.heap_extends))
    obtain ⟨-, bytes0, hst0⟩ := read_payload_stream ev126
    obtain ⟨_, rem1, _, _, -, hr1, -, hs1, -, -⟩ := Decl.get_address_spec hst0 ev148
    injection hr1 with h1; injection h1 with _ h2; injection h2 with e1 _
    subst e1
    obtain ⟨_, bytes2, -, -, hs2, -⟩ :=
      get_count_spec (L1.Stream.mono (ev194.heap_extends.trans evOrd.heap_extends) hs1) ev231
    obtain ⟨_, advAs, bytes3, -, -, hadvRep, hs3, -⟩ := Decl.get_addrs_spec hs2 ev266
    obtain ⟨nw, bytes4, -, hnwEq, hs4, -⟩ := get_count_spec hs3 ev309
    subst hnwEq
    have ext297 : Heap.Extends h _ :=
      ext184.trans (evOrd.heap_extends.trans (ev231.heap_extends.trans
        (ev266.heap_extends.trans ev309.heap_extends)))
    have ext423 := ev309.heap_extends.trans (evWs.heap_extends.trans
      (evAsb.heap_extends.trans evCrr.heap_extends))
    have extAsbFro : Heap.Extends _ _ :=
      evCrr.heap_extends.trans <| evAdv.heap_extends.trans <| ev513.heap_extends.trans <|
        ev601.heap_extends.trans <| ev634.heap_extends.trans <| ev664.heap_extends.trans <|
        ev686.heap_extends.trans <| ev716.heap_extends.trans <| ev759.heap_extends.trans <|
        ev817.heap_extends.trans <| ev796.heap_extends.trans <| ev852.heap_extends.trans <|
        evNoRole.heap_extends.trans <| ev874.heap_extends.trans <| ev896.heap_extends.trans <|
        ev960.heap_extends.trans <| ev939.heap_extends.trans <| ev1011.heap_extends.trans <|
        ev990.heap_extends.trans <| evM1.heap_extends.trans <| evCat.heap_extends.trans <|
        evM2.heap_extends.trans <| evM3.heap_extends.trans <| ev1203.heap_extends.trans <|
        evFlat.heap_extends.trans <| ev1246.heap_extends.trans <| evFlen.heap_extends.trans <|
        evZ1.heap_extends.trans <| evZ2.heap_extends.trans evVg.heap_extends
    exact ⟨advAs, h, h', rc, xb, xrb, r, hrc, hxb, hxrb, ev,
      ⟨hpath, _, _, _, _, ext184, evOrd, _, _, nw, bytes4, _, _, _, _, ext297, hs4, evWs,
        _, _, _, evAsb, _, _, _, evCrr, _, _, _, _, evAdv,
        RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext423 hadvRep,
        _, _, _, _, extAsbFro, evFro,
        (fun cl hcl => by rw [hc1474]; simp [hcl]),
        (fun cl hcl => by rw [hc1474]; simp [hcl]),
        (fun cl hcl => by rw [hc1474]; simp [hcl]),
        (fun cl hcl => by rw [hc1474]; simp [hcl]),
        (fun cl hcl => by rw [hc1474]; simp [hcl]),
        fun _ hc => nomatch hc⟩,
      hmem, hsub⟩

/-- **Unpack every guard of an observed `FamilyCallExact`**. -/
theorem FamilyCallExact.unpack {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} {advAs : List Bytes.Address}
    (hC : CollisionFreeRun calls E₀) (hbd : IxVM.Consistency.Bounded calls)
    (hex : FamilyCallExact calls bAddr t B rb lim cs advAs) :
    ∃ outs, FamilyCallUnpacked calls bAddr t E₀ B rb lim cs advAs outs := by
  obtain ⟨h, h', rc, xb, xrb, r, hrc, ⟨bB, hbB, rfl⟩, ⟨bR, hbR, rfl⟩, ev, g, hmemEv, hsub⟩ := hex
  obtain ⟨path, m_ord0, m_ord1, v_ord, cs_ord, ext184, evOrd,
    m297, m332, nw, bytes4, x_s4, x_out, x_s5, csWs, ext297, hs4, evWs,
    x_wset, m391, csAsb, evAsb,
    v_crr, m423, csCrr, evCrr,
    x_adv, v_adv, m453, csAdv, evAdv, hadvP,
    m_fro0, m_fro1, v_fro, csFro, ext391_fro, evFro,
    subWs, subAsb, subCrr, subAdv, subFro, _⟩ := g
  have hrbOrd : Claim.OpOrderedAt t lim (Core.ixAddr bR) :=
    assert_in_order_spec (hrc.mono ext184)
      ⟨bR, Bytes.repAddressRef_heapMono₂ Core.addrTy ext184 hbR, rfl⟩ evOrd
  have hsubWs : ∀ cl ∈ csWs, cl ∈ calls := fun cl hcl => hsub cl (subWs cl hcl)
  have hsubCrr : ∀ cl ∈ csCrr, cl ∈ calls := fun cl hcl => hsub cl (subCrr cl hcl)
  have hsubAdv : ∀ cl ∈ csAdv, cl ∈ calls := fun cl hcl => hsub cl (subAdv cl hcl)
  have hsubFro : ∀ cl ∈ csFro, cl ∈ calls := fun cl hcl => hsub cl (subFro cl hcl)
  obtain ⟨outs, -, houtsRep, -, houtsOrd, -, houtsDc⟩ :=
    check_witnesses_spec hC (ZMod.val (nw : F)) rfl (hrc.mono ext297)
      (Bytes.repAddressRef_heapMono₂ Core.addrTy ext297 hbB) hs4 evWs hsubWs
  obtain ⟨extAsb, hwsetRev⟩ := Claim.addr_set_build_spec houtsRep (Claim.RepAddrSet.nil m332) evAsb
  have hwset : Claim.RepAddrSet m391 (outs.map Core.ixAddr) x_wset := by
    obtain ⟨es, hbst, hlen, hmem⟩ := hwsetRev
    refine ⟨es, hbst, hlen, fun b => ?_⟩
    rw [hmem b]
    simp [List.mem_reverse]
  have ext391 : Heap.Extends h m391 := ext297.trans (evWs.heap_extends.trans extAsb)
  have houts391 := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) extAsb houtsRep
  have hcrr := container_recs_refs_spec hC hbd outs (hrc.mono ext391) houts391 hwset evCrr hsubCrr
  have ext423 : Heap.Extends h m423 := ext391.trans evCrr.heap_extends
  have hadvSpec := check_advice_records_indexed_spec hC.runStore hC.hashedStored
    (hrc.mono ext423) hadvP (hwset.mono evCrr.heap_extends) evAdv hsubAdv
  have extFro := ext391.trans ext391_fro
  have hfro := family_refs_ok_spec hC.runStore hC.hashedStored (hrc.mono extFro)
    ⟨bR, Bytes.repAddressRef_heapMono₂ Core.addrTy extFro hbR, rfl⟩
    ⟨bB, Bytes.repAddressRef_heapMono₂ Core.addrTy extFro hbB, rfl⟩
    (hwset.mono ext391_fro) evFro hsubFro
  refine ⟨outs, ⟨hrbOrd, ?_, ?_, ?_, hadvSpec, hfro⟩⟩
  · intro w hw
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
    exact houtsOrd b hb
  · intro w hw
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
    rcases houtsDc b hb with h0 | h1 | hdw | h3
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · obtain ⟨-, -, -, hcrWit⟩ := hdw.extract hC (hrc.mono ext297)
        (Bytes.repAddressRef_heapMono₂ Core.addrTy ext297 hbB) hs4 hsubWs
      exact Or.inr (Or.inr (Or.inl ⟨⟨h, h', rc, xb, xrb, r, hrc, ⟨bB, hbB, rfl⟩, ⟨bR, hbR, rfl⟩,
        ev, ⟨path, m_ord0, m_ord1, v_ord, cs_ord, ext184, evOrd,
          m297, m332, nw, bytes4, x_s4, x_out, x_s5, csWs, ext297, hs4, evWs,
          x_wset, m391, csAsb, evAsb, v_crr, m423, csCrr, evCrr,
          x_adv, v_adv, m453, csAdv, evAdv, hadvP,
          m_fro0, m_fro1, v_fro, csFro, ext391_fro, evFro,
          subWs, subAsb, subCrr, subAdv, subFro,
          fun _ heq => by cases heq; exact hdw⟩, hmemEv, hsub⟩, hcrWit⟩))
    · exact Or.inr (Or.inr (Or.inr h3))
  · intro w hw
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
    exact hcrr b hb

/-- **Unpack a `DirectContOwn` witness directly from its `CheckFamilyGuards`**:
gives `x ∈ outs.map ixAddr`, `OpOrderedAt`, `ContainerRecIn`, `check_container_rec` at `ib` with
`PathPos E₀ B ib`, `ContainerRefsFacts`, and witness classification on the same `outs`. -/
theorem DirectContOwn.unpack {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} {advAs : List Bytes.Address} {x : _root_.Address}
    (hC : CollisionFreeRun calls E₀) (hbd : IxVM.Consistency.Bounded calls)
    (hdc : DirectContOwn calls bAddr t B rb lim cs advAs x) :
    ∃ (outs : List Bytes.Address),
      x ∈ outs.map Core.ixAddr ∧
      Claim.OpOrderedAt t lim x ∧
      ContainerRecIn cs x ∧
      (∃ ib, PathPos E₀ B ib ∧
        ∃ (h₁ h₂ : Heap F) (rc₁ xx₁ xib₁ r₁ : SourceValue F) (cs₁ : List (Call F)),
          Claim.RCLimRep t bAddr lim h₁ rc₁ ∧
          Core.S0.addr h₁ xx₁ x ∧ Core.S0.addr h₁ xib₁ ib ∧
          ObsFn Obs.W "KernelModeled::check_container_rec" [rc₁, xx₁, xib₁] h₁ r₁ h₂ cs₁ ∧
          (∀ cl ∈ cs₁, cl ∈ calls)) ∧
      ContainerRefsFacts calls bAddr t E₀ lim (outs.map Core.ixAddr) x ∧
      (∀ w ∈ outs.map Core.ixAddr, Claim.OpOrderedAt t lim w) ∧
      (∀ w ∈ outs.map Core.ixAddr,
        (∃ ro : Ix.Kernel.Role, t.addressOf? ro = some w ∧
          Ix.SpecDigest.groupOf ro < 6 ∧
          (RoleVal.roleWalksBound ro = true ∨ RoleVal.isQuotRole ro = true)) ∨
        (PathPos E₀ B w ∧ Claim.NotBlockIn calls w ∧
          ∃ c, recordOf E₀ w = some c ∧
            (IsProj c → usedRefIdxs c = [] ∧
              ∃ cb, recordOf E₀ (Ix.Cert.ownerOf w c) = some cb ∧
                ConstAddrOf (Ix.Cert.ownerOf w c) cb w)) ∨
        (DirectContOwn calls bAddr t B rb lim cs advAs w ∧
          ∃ ib, PathPos E₀ B ib ∧
            ∃ (h₁ h₂ : Heap F) (rc₁ xx₁ xib₁ r₁ : SourceValue F) (cs₁ : List (Call F)),
              Claim.RCLimRep t bAddr lim h₁ rc₁ ∧
              Core.S0.addr h₁ xx₁ w ∧ Core.S0.addr h₁ xib₁ ib ∧
              ObsFn Obs.W "KernelModeled::check_container_rec" [rc₁, xx₁, xib₁] h₁ r₁ h₂ cs₁ ∧
              (∀ cl ∈ cs₁, cl ∈ calls)) ∨
        (∃ ib c cib, PathPos E₀ B ib ∧ recordOf E₀ w = some c ∧ IsProj c ∧
          Ix.Cert.ownerOf w c = ib ∧ usedRefIdxs c = [] ∧
          recordOf E₀ ib = some cib ∧ ConstAddrOf ib cib w)) := by
  obtain ⟨h, h', rc, xb, xrb, r, hrc, ⟨bB, hbB, rfl⟩, ⟨bR, hbR, rfl⟩, ev, g, hmemEv, hsub⟩ := hdc
  obtain ⟨path, m_ord0, m_ord1, v_ord, cs_ord, ext184, evOrd,
    m297, m332, nw, bytes4, x_s4, x_out, x_s5, csWs, ext297, hs4, evWs,
    x_wset, m391, csAsb, evAsb,
    v_crr, m423, csCrr, evCrr,
    x_adv, v_adv, m453, csAdv, evAdv, hadvP,
    m_fro0, m_fro1, v_fro, csFro, ext391_fro, evFro,
    subWs, subAsb, subCrr, subAdv, subFro, hcont⟩ := g
  have hdw := hcont x rfl
  have hsubWs : ∀ cl ∈ csWs, cl ∈ calls := fun cl hcl => hsub cl (subWs cl hcl)
  have hsubCrr : ∀ cl ∈ csCrr, cl ∈ calls := fun cl hcl => hsub cl (subCrr cl hcl)
  obtain ⟨outs, -, houtsRep, -, houtsOrd, -, houtsDc⟩ :=
    check_witnesses_spec hC (ZMod.val (nw : F)) rfl (hrc.mono ext297)
      (Bytes.repAddressRef_heapMono₂ Core.addrTy ext297 hbB) hs4 evWs hsubWs
  obtain ⟨⟨outs', houtsRep', hxMem'⟩, hordX, hcrWs, hcrWit⟩ :=
    hdw.extract hC (hrc.mono ext297)
      (Bytes.repAddressRef_heapMono₂ Core.addrTy ext297 hbB) hs4 hsubWs
  have eouts : outs' = outs := addrList_rep_det houtsRep' houtsRep
  subst eouts
  obtain ⟨extAsb, hwsetRev⟩ := Claim.addr_set_build_spec houtsRep (Claim.RepAddrSet.nil m332) evAsb
  have hwset : Claim.RepAddrSet m391 (outs'.map Core.ixAddr) x_wset := by
    obtain ⟨es, hbst, hlen, hmem⟩ := hwsetRev
    refine ⟨es, hbst, hlen, fun b => ?_⟩
    rw [hmem b]; simp [List.mem_reverse]
  have ext391 : Heap.Extends h m391 := ext297.trans (evWs.heap_extends.trans extAsb)
  have houts391 := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) extAsb houtsRep
  have hcrr := container_recs_refs_spec hC hbd outs' (hrc.mono ext391) houts391 hwset evCrr hsubCrr
  obtain ⟨bx, hbx, rfl⟩ := List.mem_map.mp hxMem'
  refine ⟨outs', List.mem_map_of_mem hbx, hordX, ?_, hcrWit, hcrr bx hbx, ?_, ?_⟩
  · obtain ⟨rc₁, xa₁, ib₁, h₁, hmem₁, hxa₁⟩ := hcrWs
    exact ⟨rc₁, xa₁, ib₁, h₁, subWs _ hmem₁, hxa₁⟩
  · intro w hw
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
    exact houtsOrd b hb
  · intro w hw
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
    rcases houtsDc b hb with h0 | h1 | hdwW | h3
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · obtain ⟨-, -, -, hcrW⟩ := hdwW.extract hC (hrc.mono ext297)
        (Bytes.repAddressRef_heapMono₂ Core.addrTy ext297 hbB) hs4 hsubWs
      exact Or.inr (Or.inr (Or.inl ⟨⟨h, h', rc, xb, xrb, r, hrc, ⟨bB, hbB, rfl⟩, ⟨bR, hbR, rfl⟩,
        ev, ⟨path, m_ord0, m_ord1, v_ord, cs_ord, ext184, evOrd,
          m297, m332, nw, bytes4, x_s4, x_out, x_s5, csWs, ext297, hs4, evWs,
          x_wset, m391, csAsb, evAsb, v_crr, m423, csCrr, evCrr,
          x_adv, v_adv, m453, csAdv, evAdv, hadvP,
          m_fro0, m_fro1, v_fro, csFro, ext391_fro, evFro,
          subWs, subAsb, subCrr, subAdv, subFro,
          fun _ heq => by cases heq; exact hdwW⟩, hmemEv, hsub⟩, hcrW⟩))
    · exact Or.inr (Or.inr (Or.inr h3))

end IxVM.Refinement.Binding
