import IxVMRefinement.Binding.FamilyReconMember
import IxVMRefinement.Binding.FamilyOfCall
import IxVMRefinement.Binding.FamilyFlatBuild
import IxVMRefinement.Binding.FamilyFlatWalk
import IxVMRefinement.Binding.FamilyFlatDerive

/-! # The entries of a block's flattened family differ, from the store

`FamilyRecon.derivedFlatAt_distinct` derives `FlatDistinct` of a derived flattened family from
`MembersSeparate`: the block's types are at different addresses, and no type of another block is
at one of them. A type's address is the BLAKE3 address of its projection record
(`memberAddr`), so both are facts of what the store holds at those addresses.

* `MembersStored E b`: the block record at `b`, if the store holds one, has fewer than `2^64`
  members and the store holds the projection record of each of its inductive types at the type's
  address.
* `membersAt_nodup`: the types of a block with `MembersStored` are at different addresses (one
  address holds one record, and the record names the type's position).
* `membersAt_apart`: two different blocks with `MembersStored` share no type address (the record
  names the block).
* `membersSeparate_ofStore`: `MembersSeparate (FlatView.ofStore t E) B` where every block of the
  store has `MembersStored`.
* `storedView t E`: the readings of the store, a block's types read only of a block with
  `MembersStored`. `storedView_le`: it answers no more than `FlatView.ofStore t E`.
  `membersSeparate_storedView`: `MembersSeparate (storedView t E) B`, with no premise.
* `StoredDerivedFlat t E B off es`: `es` is derived from `B` over `storedView t E` at the
  block's elimination offset. `StoredDerivedFlat.blockDerivedFlat`,
  **`StoredDerivedFlat.flatDistinct`**, `flatDistinct_of_storedView`: a family the derivation
  over `FlatView.ofStore t E` answers has different entries when the derivation over
  `storedView t E` answers at all.
* `membersStored_of_hashed`, `membersStored_of_call`, `membersStored_of_famBlockRecord`: a block
  whose types' projection records the run hashed has `MembersStored`; so has the block of an
  observed family check (`Ingress::build_recur_addrs` hashes each projection record; the loaded
  block record is below `2^33`), and a modeled block's record with fewer than `2^64` members.
* `flat_originals_walk_members`, `build_flat_originals_members`,
  `membersStored_of_build_flat_originals`: `KernelCheck::build_flat_originals` lists the
  addresses of the inductive types of a block of the store and hashes the projection record of
  each (`Ingress::projection_addr`), so the block it lists has `MembersStored`.
* `flatMembersAnswersIn_storedView`: `FlatMembersAnswersIn root (storedView t E₀)`, the answer of
  `KernelCheck::build_flat_originals` the nested walk's refinement asks, among the calls of a
  run with its store.
* `nestedWalkSpec_storedView`: the reading of `KernelModeled::nested_walk` over `storedView`
  (`NestedWalkSpec`), from the answers of the loads over the store's readings, the membership
  test (`AuxEntryInSpecIn`) and the depth bound (`ScanDepthIn`); `NestedWalkSpec.ofStore`: it is
  a reading over `FlatView.ofStore`.
* `storedDerivedFlat_of_checks`, `flatDistinct_of_checks`: an observed `check_nested_aux` on the
  flattened family of a block with `MembersStored` gives `StoredDerivedFlat`, hence
  `FlatDistinct`.
* **`flatDistinct_of_call`**: on the events of an observed family check
  (`blockDerivedFlat_of_checkFamily`'s premises, the reading of `nested_walk` taken over
  `storedView`), the entries `es` with `BlockDerivedFlat t E₀ B off es` have `FlatDistinct es`.

`MembersSeparate (FlatView.ofStore t E) B` itself does not follow from a run: its second field
ranges over every block record of the store, and a block whose types' projection records the run
never hashed has type addresses that are hashes of byte strings outside the run, about which the
run's store says nothing. The derivation reads a block's types only through
`KernelCheck::build_flat_originals`, which hashes those records; `storedView` is the view that
keeps that. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option autoImplicit false

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency
open IxVM.Refinement.Binding.FamilyFlat
open IxVM.Refinement.Core (W KExpr KLevel KKey kexprEnum kexprListEnum addrTy ixAddr)
open IxVM (F)

/-! ## A block's types' projection records -/

/-- **The store holds the projection records of the block at `b`'s inductive types**, each at
the type's address, and the block has fewer than `2^64` members. -/
def MembersStored (E : Ixon.Env) (b : _root_.Address) : Prop :=
  ∀ cb ms, recordOf E b = some cb → cb.info = .muts ms →
    ms.size < UInt64.size ∧
    ∀ i ind, ms[i]? = some (Ixon.MutConst.indc ind) →
      recordOf E (memberAddr b i (.indc ind)) = some (memberProjection b i (.indc ind))

/-- An inductive type's projection record names its block and its position. -/
theorem memberProjection_indc_inj {b B : _root_.Address} {i j : Nat} {x y : Ixon.Inductive}
    (hi : i < UInt64.size) (hj : j < UInt64.size)
    (h : memberProjection b i (.indc x) = memberProjection B j (.indc y)) : b = B ∧ i = j := by
  have h1 : (memberProjection b i (.indc x)).info = .iPrj ⟨i.toUInt64, b⟩ := rfl
  have h2 : (memberProjection B j (.indc y)).info = .iPrj ⟨j.toUInt64, B⟩ := rfl
  rw [h, h2] at h1
  injection h1 with h3
  injection h3 with h4 h5
  have h6 := congrArg UInt64.toNat h4
  rw [FamilyFlatRecord.toUInt64_toNat_of_lt hi, FamilyFlatRecord.toUInt64_toNat_of_lt hj] at h6
  exact ⟨h5.symm, h6.symm⟩

theorem mem_indcAddrs {b a : _root_.Address} :
    ∀ (l : List Ixon.MutConst) (k : Nat), a ∈ indcAddrs b k l →
      ∃ j ind, l[j]? = some (Ixon.MutConst.indc ind) ∧ a = memberAddr b (k + j) (.indc ind) := by
  intro l
  induction l with
  | nil => intro k h; simp [indcAddrs] at h
  | cons m l ih =>
    intro k h
    have hrest : a ∈ indcAddrs b (k + 1) l →
        ∃ j ind, (m :: l)[j]? = some (Ixon.MutConst.indc ind) ∧
          a = memberAddr b (k + j) (.indc ind) := by
      intro h'
      obtain ⟨j, ind, hj, ha⟩ := ih (k + 1) h'
      refine ⟨j + 1, ind, by simpa using hj, ?_⟩
      rw [ha, show k + 1 + j = k + (j + 1) by omega]
    cases m with
    | indc ind =>
      simp only [indcAddrs] at h
      rcases List.mem_cons.mp h with h | h
      · exact ⟨0, ind, rfl, h⟩
      · exact hrest h
    | defn d => simp only [indcAddrs] at h; exact hrest h
    | recr r => simp only [indcAddrs] at h; exact hrest h

theorem indcAddrs_nodup {b : _root_.Address} :
    ∀ (l : List Ixon.MutConst) (k : Nat),
      (∀ i j x y, l[i]? = some (Ixon.MutConst.indc x) → l[j]? = some (Ixon.MutConst.indc y) →
        memberAddr b (k + i) (.indc x) = memberAddr b (k + j) (.indc y) → i = j) →
      (indcAddrs b k l).Nodup := by
  intro l
  induction l with
  | nil => intro k _; simp [indcAddrs]
  | cons m l ih =>
    intro k hinj
    have ih' : (indcAddrs b (k + 1) l).Nodup := by
      apply ih (k + 1)
      intro i j x y hi hj he
      have := hinj (i + 1) (j + 1) x y (by simpa using hi) (by simpa using hj)
        (by rw [show k + (i + 1) = k + 1 + i by omega, show k + (j + 1) = k + 1 + j by omega]
            exact he)
      omega
    cases m with
    | indc ind =>
      simp only [indcAddrs]
      rw [List.nodup_cons]
      refine ⟨fun hmem => ?_, ih'⟩
      obtain ⟨j, y, hj, ha⟩ := mem_indcAddrs l (k + 1) hmem
      have := hinj 0 (j + 1) ind y rfl (by simpa using hj)
        (by rw [show k + (j + 1) = k + 1 + j by omega]; exact ha)
      omega
    | defn d => simpa only [indcAddrs] using ih'
    | recr r => simpa only [indcAddrs] using ih'

theorem membersAt_eq_some {E : Ixon.Env} {b : _root_.Address} {l : List _root_.Address}
    (h : membersAt E b = some l) :
    ∃ cb ms, recordOf E b = some cb ∧ cb.info = .muts ms ∧ l = indcAddrs b 0 ms.toList := by
  unfold membersAt at h
  cases hc : recordOf E b with
  | none => simp [hc] at h
  | some cb =>
    simp only [hc] at h
    cases hi : cb.info with
    | muts ms =>
      simp only [hi, Option.some.injEq] at h
      exact ⟨cb, ms, rfl, hi, h.symm⟩
    | _ => simp [hi] at h

/-- A type address of a block with `MembersStored` holds the projection record of a position of
the block. -/
theorem membersAt_mem {E : Ixon.Env} {b a : _root_.Address} {l : List _root_.Address}
    (hs : MembersStored E b) (h : membersAt E b = some l) (ha : a ∈ l) :
    ∃ j ind, j < UInt64.size ∧ a = memberAddr b j (.indc ind) ∧
      recordOf E a = some (memberProjection b j (.indc ind)) := by
  obtain ⟨cb, ms, hcb, hms, rfl⟩ := membersAt_eq_some h
  obtain ⟨hsz, hrec⟩ := hs cb ms hcb hms
  obtain ⟨j, ind, hj, rfl⟩ := mem_indcAddrs ms.toList 0 ha
  rw [Array.getElem?_toList] at hj
  have hjlt : j < ms.size := (Array.getElem?_eq_some_iff.mp hj).1
  rw [Nat.zero_add]
  exact ⟨j, ind, Nat.lt_trans hjlt hsz, rfl, hrec j ind hj⟩

/-- **The types of a block whose projection records the store holds are at different
addresses.** -/
theorem membersAt_nodup {E : Ixon.Env} {B : _root_.Address} {l : List _root_.Address}
    (hs : MembersStored E B) (h : membersAt E B = some l) : l.Nodup := by
  obtain ⟨cb, ms, hcb, hms, rfl⟩ := membersAt_eq_some h
  obtain ⟨hsz, hrec⟩ := hs cb ms hcb hms
  apply indcAddrs_nodup
  intro i j x y hi hj he
  rw [Array.getElem?_toList] at hi hj
  have hilt : i < ms.size := (Array.getElem?_eq_some_iff.mp hi).1
  have hjlt : j < ms.size := (Array.getElem?_eq_some_iff.mp hj).1
  rw [Nat.zero_add, Nat.zero_add] at he
  have h1 := hrec i x hi
  have h2 := hrec j y hj
  rw [he, h2] at h1
  exact (memberProjection_indc_inj (Nat.lt_trans hjlt hsz) (Nat.lt_trans hilt hsz)
    (Option.some.inj h1)).2.symm

/-- **Two different blocks whose types' projection records the store holds share no type
address.** -/
theorem membersAt_apart {E : Ixon.Env} {B b : _root_.Address} {l lb : List _root_.Address}
    (hB : MembersStored E B) (hb : MembersStored E b) (hne : (b == B) = false)
    (h : membersAt E B = some l) (h' : membersAt E b = some lb) : ∀ a ∈ lb, a ∉ l := by
  intro a hab haB
  obtain ⟨j, y, hj, -, hrj⟩ := membersAt_mem hb h' hab
  obtain ⟨i, x, hi, -, hri⟩ := membersAt_mem hB h haB
  rw [hrj] at hri
  have := (memberProjection_indc_inj hj hi (Option.some.inj hri)).1
  rw [this] at hne
  simp at hne

/-- **`MembersSeparate` of the store's readings**, where the store holds the projection records
of the types of every block it holds. -/
theorem membersSeparate_ofStore {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    (hall : ∀ b, MembersStored E b) (B : _root_.Address) :
    MembersSeparate (FlatView.ofStore t E) B where
  nodup ms h := membersAt_nodup (hall B) h
  apart b ms msb hne h h' := membersAt_apart (hall B) (hall b) hne h h'

/-! ## The readings of the stored blocks -/

open Classical in
/-- **The readings of the store `E`, a block's types read only where the store holds their
projection records** (`MembersStored`). The circuit's `build_flat_originals` hashes them. -/
noncomputable def storedView (t : Ix.Kernel.RoleTable) (E : Ixon.Env) : FlatView :=
  ⟨indInfoAt E, ctorTypeAt t E, fun b => if MembersStored E b then membersAt E b else none,
    keyAddr t⟩

theorem storedView_members {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {b : _root_.Address}
    {l : List _root_.Address} (h : (storedView t E).members b = some l) :
    MembersStored E b ∧ membersAt E b = some l := by
  unfold storedView at h
  simp only at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

theorem storedView_members_of {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {b : _root_.Address}
    (hs : MembersStored E b) : (storedView t E).members b = membersAt E b := by
  unfold storedView
  simp only [hs, ite_true]

/-- The readings of the stored blocks are readings of the store. -/
theorem storedView_le (t : Ix.Kernel.RoleTable) (E : Ixon.Env) :
    (storedView t E).Le (FlatView.ofStore t E) where
  ci a x h := h
  ctorType b i c x h := h
  members b x h := (storedView_members h).2
  addr k x h := h

/-- **`MembersSeparate` of the readings of the stored blocks.** -/
theorem membersSeparate_storedView (t : Ix.Kernel.RoleTable) (E : Ixon.Env)
    (B : _root_.Address) : MembersSeparate (storedView t E) B where
  nodup ms h := membersAt_nodup (storedView_members h).1 (storedView_members h).2
  apart b ms msb hne h h' :=
    membersAt_apart (storedView_members h).1 (storedView_members h').1 hne
      (storedView_members h).2 (storedView_members h').2

/-- **`es` is the flattened family derived from the block `B` over the stored blocks of `E`**,
at the block's elimination offset. -/
def StoredDerivedFlat (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (B : _root_.Address) (off : Nat)
    (es : List FlatEntry) : Prop :=
  BlockElim t E B off ∧ ∃ n, derivedFlatAt (storedView t E) B off n = some es

theorem StoredDerivedFlat.blockDerivedFlat {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {B : _root_.Address} {off : Nat} {es : List FlatEntry} (h : StoredDerivedFlat t E B off es) :
    BlockDerivedFlat t E B off es :=
  ⟨h.1, h.2.imp fun n hn => derivedFlatAt_le (storedView_le t E) hn⟩

/-- **The flattened family derived over the stored blocks has different entries.** -/
theorem StoredDerivedFlat.flatDistinct {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {B : _root_.Address} {off : Nat} {es : List FlatEntry} (h : StoredDerivedFlat t E B off es) :
    FlatDistinct es := by
  obtain ⟨-, n, hn⟩ := h
  exact derivedFlatAt_distinct (membersSeparate_storedView t E B) hn

/-- **The flattened family derived from a block has different entries**, where the derivation
over the stored blocks answers at some fuel. -/
theorem flatDistinct_of_storedView {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {B : _root_.Address}
    {off : Nat} {es es' : List FlatEntry} {n : Nat} (h : BlockDerivedFlat t E B off es)
    (hst : derivedFlatAt (storedView t E) B off n = some es') : FlatDistinct es := by
  obtain ⟨-, n', hn'⟩ := h
  have e : es' = es :=
    derivedFlatAt_unique (derivedFlatAt_le (storedView_le t E) hst) hn'
  subst e
  exact derivedFlatAt_distinct (membersSeparate_storedView t E B) hst

/-- **The flattened family derived from a block has different entries**, where the store holds
the projection records of the types of every block it holds. -/
theorem flatDistinct_of_allStored {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {B : _root_.Address}
    {off : Nat} {es : List FlatEntry} (hall : ∀ b, MembersStored E b)
    (h : BlockDerivedFlat t E B off es) : FlatDistinct es := by
  obtain ⟨-, n, hn⟩ := h
  exact derivedFlatAt_distinct (membersSeparate_ofStore hall B) hn

/-! ## The blocks the circuit lists -/

section Run

open IxVM.Refinement.Core
open IxVM.Refinement.Binding.FamilyOf
open IxVM.Refinement.Binding.FamilyOfCall
open IxVM.Refinement.Typing

variable {calls : List (Call F)} {E₀ : Ixon.Env}

/-- **A block whose inductive types' projection records the run hashed has `MembersStored`.** -/
theorem membersStored_of_hashed (hH : LoadedReads.HashedRecordsStored calls E₀)
    {bP : Bytes.Address} {cP : Ixon.Constant} {mP : Array Ixon.MutConst}
    (hcP : recordOf E₀ (ixAddr bP) = some cP) (hmP : cP.info = .muts mP)
    (hsz : mP.size < 8589934592)
    (hh : ∀ j ind, mP[j]? = some (Ixon.MutConst.indc ind) → Hashed calls (Ixon.serConstant
      ⟨Core.Specs.Callees.memberProjInfo (ixAddr bP) j (.indc ind), #[], #[], #[], #[]⟩)) :
    MembersStored E₀ (ixAddr bP) := by
  intro cb ms hcb hms
  have e1 : cb = cP := Option.some.inj (hcb.symm.trans hcP)
  subst e1
  have e2 : ms = mP := Ixon.ConstantInfo.muts.inj (hms.symm.trans hmP)
  subst e2
  refine ⟨by have : UInt64.size = 18446744073709551616 := rfl; omega, ?_⟩
  intro i ind hi
  have hwf : (⟨Core.Specs.Callees.memberProjInfo (ixAddr bP) i (.indc ind), #[], #[], #[],
      #[]⟩ : Ixon.Constant).wireWF := L1.projConstant_wireWF_iPrj i.toUInt64 bP
  have hrecraw := Claim.recordOf_of_hashed hH (hh i ind hi)
    (serConstant_iprj_size_lt i.toUInt64 bP) (Ixon.Verify.deConstantExact_serConstant _ hwf)
  rw [LoadedReads.memberAddr_eq_projAddr]
  exact hrecraw

/-- **The block of an observed family check has `MembersStored`**: the check hashes each of its
types' projection records, and the block record it loads has fewer than `2^33` members. -/
theorem membersStored_of_call {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {B rb : _root_.Address} {lim : Option Nat} {cs : List (Call F)}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs) : MembersStored E₀ B := by
  obtain ⟨cb, ms, hcb, hms, -, hall, hmem⟩ := familyCall_block_members hS hH hfc
  obtain ⟨h, h', rc, xb, xrb, r, -, ⟨bB, hbB, rfl⟩, -, ev, -, hsub⟩ := hfc
  obtain ⟨C⟩ := FamilyAlias.checkFamily_chain ev
  have ext_0_453 : Heap.Extends h C.m453 :=
    (check_family_seg1_extends C.sg112).trans C.ext_m105_m453
  have hsubLoad : ∀ cl ∈ C.evLoadBlk.cs, cl ∈ calls :=
    fun cl hcl => hsub cl (C.evLoadBlk.sub cl hcl)
  obtain ⟨cb', ms', hbl, -⟩ :=
    Claim.load_block_head (Bytes.repAddressRef_heapMono₂ addrTy ext_0_453 hbB) C.evLoadBlk.obs
  have hres : cb.resourceSize < 8589934592 := ((hbl.mono hsubLoad).record hS hcb).2
  have hle : ms.size ≤ cb.resourceSize := Claim.muts_size_le hms
  intro cb₁ ms₁ hcb₁ hms₁
  have e1 : cb₁ = cb := Option.some.inj (hcb₁.symm.trans hcb)
  subst e1
  have e2 : ms₁ = ms := Ixon.ConstantInfo.muts.inj (hms₁.symm.trans hms)
  subst e2
  refine ⟨by have : UInt64.size = 18446744073709551616 := rfl; omega, ?_⟩
  intro i ind hi
  exact hmem i _ hi

/-- **`KernelCheck::flat_originals_walk`** over the members of a block from position `k` lists
the addresses of the block's inductive types (`indcAddrs`), and hashes the projection record of
each. -/
theorem flat_originals_walk_members {bP : Bytes.Address} {mP : Array Ixon.MutConst}
    (hsz : mP.size < 8589934592) {x_all x_blk xoff : SourceValue F} :
    ∀ (cur : List Ixon.MutConst) (k : Nat) {x_cur r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      (∀ j m, cur[j]? = some m → mP[k + j]? = some m) →
      RepList L1.mutConstListEnum L1.RepMutConst h mP.toList x_all →
      RepList L1.mutConstListEnum L1.RepMutConst h cur x_cur →
      Bytes.RepAddressRef addrTy h bP x_blk →
      ObsFn W "KernelCheck::flat_originals_walk"
        [x_all, x_cur, x_blk, xoff, .field (k : F)] h r h' cs →
      Heap.Extends h h' ∧
      RepList flatListEnum MemberAddrRep h' (indcAddrs (ixAddr bP) k cur) r ∧
      ∀ j ind, cur[j]? = some (Ixon.MutConst.indc ind) → Hashed cs (Ixon.serConstant
        ⟨Core.Specs.Callees.memberProjInfo (ixAddr bP) (k + j) (.indc ind), #[], #[], #[],
          #[]⟩) := by
  intro cur
  induction cur with
  | nil =>
    intro k x_cur r h h' cs _ _ hcur _ ev
    match Obs.«KernelCheck::flat_originals_walk».obs ev with
    | .Nil (he24 := hr) (hm23 := hh) .. =>
      rw [hr, hh]
      exact ⟨Heap.Extends.snoc _ _, Lib.rep_store_nil h, fun j ind hj => by simp at hj⟩
    | .Cons_Indc (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hcur ld
      cases he
  | cons m rest ih =>
    intro k x_cur r h h' cs hsuf hall hcur hb ev
    have hm0 : mP[k]? = some m := by simpa using hsuf 0 m rfl
    have hklt : k < mP.size := (Array.getElem?_eq_some_iff.mp hm0).1
    have hsuf' : ∀ j m', rest[j]? = some m' → mP[k + 1 + j]? = some m' := fun j m' hj => by
      have := hsuf (j + 1) m' (by simpa using hj)
      rwa [show k + (j + 1) = k + 1 + j by omega] at this
    match Obs.«KernelCheck::flat_originals_walk».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hcur ld
    | .Cons_other (cs382 := cs382) (ld12 := ld) (hne375 := hne) (op431 := op) (ev384 := evR)
        (hc433 := hc) .. =>
      obtain ⟨m', rest', he, hm, hrest⟩ := Lib.rep_cons_of_load hcur ld
      injection he with h1 h2
      subst h1 h2
      obtain rfl := binop_add_one_nat op
      obtain ⟨ext, hrep, hhash⟩ := ih (k + 1) hsuf' hall hrest hb evR
      have hhash' : ∀ j ind, rest[j]? = some (Ixon.MutConst.indc ind) → Hashed cs
          (Ixon.serConstant ⟨Core.Specs.Callees.memberProjInfo (ixAddr bP) (k + (j + 1))
            (.indc ind), #[], #[], #[], #[]⟩) := fun j ind hj => by
        rw [show k + (j + 1) = k + 1 + j by omega]
        exact Core.hashed_mono (fun c hc' => by rw [hc]; simp [hc']) (hhash j ind hj)
      cases m with
      | indc ind =>
        obtain ⟨iv, hiv, -⟩ := hm
        exact absurd hiv (hne [iv] rfl)
      | defn d =>
        refine ⟨ext, by simpa only [indcAddrs] using hrep, ?_⟩
        intro j ind hj
        cases j with
        | zero => simp at hj
        | succ j => exact hhash' j ind (by simpa using hj)
      | recr rc =>
        refine ⟨ext, by simpa only [indcAddrs] using hrep, ?_⟩
        intro j ind hj
        cases j with
        | zero => simp at hj
        | succ j => exact hhash' j ind (by simpa using hj)
    | .Cons_Indc (v68 := v68) (cs79 := cs79) (v106 := v106) (m107 := m107) (cs120 := cs120)
        (v213 := v213) (m214 := m214) (v222 := v222) (m223 := m223) (v268 := v268)
        (m295 := m295) (m315 := m315) (cs323 := cs323)
        (ld12 := ld) (ev81 := e1) (ev122 := e2) (ld116 := ld116) (sg221 := sg) (ev235 := e3)
        (he263 := hr) (hm262 := hh) (hm303 := hm3) (op372 := op) (ev325 := evR)
        (hc374 := hc) .. =>
      obtain ⟨m', rest', he, hm, hrest⟩ := Lib.rep_cons_of_load hcur ld
      injection he with h1 h2
      subst h1 h2
      cases m with
      | defn d => obtain ⟨_, hmv, -⟩ := hm; simp at hmv
      | recr rc => obtain ⟨_, hmv, -⟩ := hm; simp at hmv
      | indc ind =>
        have hkval : ((k : F)).val = k := FamilyOfCall.val_cast_lt_u58 (by omega)
        obtain ⟨ext1, -, -, mc, a, hget, ha_rep, ha_eq, hhash⟩ :=
          L1.projection_addr_hashed_spec (Route.membersRep_of_repMutConstList hall) hb e1
        rw [hkval, Array.getElem?_toList, hm0] at hget
        have hmc : mc = .indc ind := (Option.some.inj hget).symm
        subst hmc
        rw [hkval] at ha_eq hhash
        have ext2 := e2.heap_extends
        have hm214 : m214 = m107 := by
          match sg with
          | .Induct (he204 := hhs) .. => exact hhs
          | .other (he211 := hhs) .. => exact hhs
        subst hm214
        subst hm3
        obtain rfl := binop_add_one_nat op
        have ext3 := e3.heap_extends
        have ext4 : Heap.Extends m223
            (m223 ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []]) :=
          Heap.Extends.snoc _ _
        have extR := ext1.trans (ext2.trans (ext3.trans ext4))
        obtain ⟨ext5, hrep, hhashR⟩ := ih (k + 1) hsuf'
          (RepLinkedList.mono L1.repMutConst_heapMono₂ extR hall)
          (RepLinkedList.mono L1.repMutConst_heapMono₂ extR hrest)
          (Bytes.repAddressRef_heapMono₂ addrTy extR hb) evR
        rw [hr, hh]
        have hentry : MemberAddrRep m315 (memberAddr (ixAddr bP) k (.indc ind))
            (.tuple [v68, .field 0,
              .ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m223.length, v222]) :=
          ⟨v68, _, _, _, a, rfl,
            Bytes.repAddressRef_heapMono₂ addrTy (ext2.trans (ext3.trans (ext4.trans ext5))) ha_rep,
            by rw [ha_eq, LoadedReads.memberAddr_eq_projAddr]⟩
        refine ⟨extR.trans (ext5.trans (Heap.Extends.snoc _ _)), ?_, ?_⟩
        · simp only [indcAddrs]
          exact Lib.rep_store_cons memberAddrRep_heapMono₂ hentry hrep
        · intro j ind' hj
          cases j with
          | zero =>
            have : ind' = ind := by simpa using hj.symm
            subst this
            exact Core.hashed_mono (fun c hc' => by rw [hc]; simp [hc']) hhash
          | succ j =>
            rw [show k + (j + 1) = k + 1 + j by omega]
            exact Core.hashed_mono (fun c hc' => by rw [hc]; simp [hc'])
              (hhashR j ind' (by simpa using hj))

/-- **`KernelCheck::build_flat_originals`** on a block record of the store lists the addresses of
the block's inductive types (`membersAt`), and hashes the projection record of each. -/
theorem build_flat_originals_members (hS : LoadedReads.RunStore calls E₀)
    {bP : Bytes.Address} {cP : Ixon.Constant} {mP : Array Ixon.MutConst}
    (hcP : recordOf E₀ (ixAddr bP) = some cP) (hmP : cP.info = .muts mP)
    {x_blk r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hb : Bytes.RepAddressRef addrTy h bP x_blk)
    (ev : ObsFn W "KernelCheck::build_flat_originals" [x_blk, .field 0] h r h' cs)
    (hsub : ∀ c ∈ cs, c ∈ calls) :
    mP.size < 8589934592 ∧
    RepList flatListEnum MemberAddrRep h' (indcAddrs (ixAddr bP) 0 mP.toList) r ∧
    ∀ j ind, mP[j]? = some (Ixon.MutConst.indc ind) → Hashed cs (Ixon.serConstant
      ⟨Core.Specs.Callees.memberProjInfo (ixAddr bP) j (.indc ind), #[], #[], #[], #[]⟩) := by
  match Obs.«KernelCheck::build_flat_originals».obs ev with
  | .Muts (cs12 := csL) (cs92 := csW) (ev14 := evL) (ev94 := evW) (hc134 := hc) .. =>
    obtain ⟨msPtr, hxm, hlist, hlt⟩ := Decl.load_block_info hS hb evL
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hcP hmP
    have hxe := (List.cons.inj (Value.construct.inj hxm).2.2).1
    subst hxe
    have extL := evL.heap_extends
    obtain ⟨-, hrep, hhash⟩ := flat_originals_walk_members hlt mP.toList 0
      (fun j m hj => by rw [Nat.zero_add, ← Array.getElem?_toList]; exact hj) hlist hlist
      (Bytes.repAddressRef_heapMono₂ addrTy extL hb) (by simpa using evW)
    refine ⟨hlt, hrep, fun j ind hj => ?_⟩
    have := hhash j ind (by rw [Array.getElem?_toList]; exact hj)
    rw [Nat.zero_add] at this
    exact Core.hashed_mono (fun c hc' => by rw [hc]; simp [hc']) this
  | .other_Induct (cs12 := csL) (ev14 := evL) (hne135 := hne) (hc332 := hc) .. =>
    obtain ⟨msPtr, hxm, -, -⟩ := Decl.load_block_info hS hb evL
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hcP hmP
    exact absurd hxm (hne [msPtr] rfl)
  | .other_other (cs12 := csL) (ev14 := evL) (hne135 := hne) (hc345 := hc) .. =>
    obtain ⟨msPtr, hxm, -, -⟩ := Decl.load_block_info hS hb evL
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hcP hmP
    exact absurd hxm (hne [msPtr] rfl)

/-- **A block the run lists with `KernelCheck::build_flat_originals` has `MembersStored`.** -/
theorem membersStored_of_build_flat_originals (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    {bP : Bytes.Address} {cP : Ixon.Constant} {mP : Array Ixon.MutConst}
    (hcP : recordOf E₀ (ixAddr bP) = some cP) (hmP : cP.info = .muts mP)
    {x_blk r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hb : Bytes.RepAddressRef addrTy h bP x_blk)
    (ev : ObsFn W "KernelCheck::build_flat_originals" [x_blk, .field 0] h r h' cs)
    (hsub : ∀ c ∈ cs, c ∈ calls) : MembersStored E₀ (ixAddr bP) := by
  obtain ⟨hlt, -, hhash⟩ := build_flat_originals_members hS hcP hmP hb ev hsub
  exact membersStored_of_hashed hH hcP hmP hlt
    (fun j ind hj => Core.hashed_mono hsub (hhash j ind hj))

/-- **`KernelCheck::build_flat_originals` answers the types `storedView` reads**, among the
calls of the run: the block it lists is a block of the store whose types' projection records it
hashes. -/
theorem flatMembersAnswersIn_storedView {t : Ix.Kernel.RoleTable}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {root : List (Call F)} (hroot : ∀ c ∈ root, c ∈ calls) :
    FlatMembersAnswersIn root (storedView t E₀) := by
  intro xblk r h m cs ba a d hb ev hsub hci hba
  obtain ⟨cb, ms, hcb, hms⟩ := FamilyFlatBuild.indInfoAt_block (E := E₀) hci
  rw [← hba] at hcb
  have hsub' : ∀ c ∈ cs, c ∈ calls := fun c hc => hroot c (hsub c hc)
  obtain ⟨hlt, hrep, hhash⟩ := build_flat_originals_members hS hcb hms hb ev hsub'
  have hst : MembersStored E₀ (ixAddr ba) :=
    membersStored_of_hashed hH hcb hms hlt (fun j ind hj => Core.hashed_mono hsub' (hhash j ind hj))
  refine ⟨indcAddrs (ixAddr ba) 0 ms.toList, ?_, hrep⟩
  rw [← hba, storedView_members_of hst]
  unfold membersAt
  simp only [hcb, hms]

/-! ## The family check's derivation is over the stored blocks -/

theorem originals_storedView (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (off : Nat) :
    ∀ ms : List _root_.Address,
      originals (storedView t E) off ms = originals (FlatView.ofStore t E) off ms := by
  have hci : (storedView t E).ci = (FlatView.ofStore t E).ci := rfl
  intro ms
  induction ms with
  | nil => rfl
  | cons a as ih => simp only [originals, hci, ih]

/-- **A modeled block's record has `MembersStored`**, the block having fewer than `2^64`
members. -/
theorem membersStored_of_famBlockRecord {B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} (hB : FamBlockRecord E₀ B cb ms) (hsz : ms.size < UInt64.size) :
    MembersStored E₀ B := by
  intro cb₁ ms₁ hcb₁ hms₁
  have e1 : cb₁ = cb := Option.some.inj (hcb₁.symm.trans hB.record)
  subst e1
  have e2 : ms₁ = ms := Ixon.ConstantInfo.muts.inj (hms₁.symm.trans hB.muts)
  subst e2
  exact ⟨hsz, fun i ind hi => hB.members i _ hi⟩

/-- **`KernelModeled::nested_walk` walks over the stored blocks** (`NestedWalkSpec` at
`storedView`), among the calls `root` of a bounded run: from the answers of the loads over the
store's readings, with `KernelCheck::build_flat_originals` answered here
(`flatMembersAnswersIn_storedView`). -/
theorem nestedWalkSpec_storedView {κ : _root_.Address → KKey} {t : Ix.Kernel.RoleTable}
    {root : List (Call F)} {S : _root_.Address → Prop} {B : _root_.Address}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hroot : ∀ c ∈ root, c ∈ calls) (hbd : Bounded root)
    (hA : FlatAddrOf κ (FlatView.ofStore t E₀))
    (hI : FlatIndAnswersIn root (FlatView.ofStore t E₀))
    (hC : FlatCtorAnswersIn root S κ (FlatView.ofStore t E₀))
    (aux_entry_in : AuxEntryInSpecIn root κ) (hdepth : ScanDepthIn root)
    (hSb : ∀ a d, indInfoAt E₀ a = some (some d) → S d.blk) :
    NestedWalkSpec κ (storedView t E₀) B root := by
  have hA' : FlatAddrOf κ (storedView t E₀) := hA
  have hI' : FlatIndAnswersIn root (storedView t E₀) := hI
  have hC' : FlatCtorAnswersIn root S κ (storedView t E₀) := hC
  intro b acc xb xacc r h h' cs hb hB hacc ev _ hsub
  have ev' : ObsFn W "KernelModeled::nested_walk" [xb, xacc, .field ((0 : Nat) : F)]
      h r h' cs := by simpa using ev
  obtain ⟨-, es, hes, n, hn⟩ := nested_walk_spec hA' hI' hC'
    (flatMembersAnswersIn_storedView hS hH hroot) (occMentionsSpecIn_of_answers hA' hI')
    aux_entry_in hdepth hSb ev' (RomBound.bounded_mono hbd hsub) hsub (Nat.zero_le _) hb hB hacc
  exact ⟨n, es, hn, hes⟩

/-- A reading of `nested_walk` over the stored blocks is one over the store. -/
theorem NestedWalkSpec.ofStore {κ : _root_.Address → KKey} {t : Ix.Kernel.RoleTable}
    {root : List (Call F)} {B : _root_.Address}
    (h : NestedWalkSpec κ (storedView t E₀) B root) :
    NestedWalkSpec κ (FlatView.ofStore t E₀) B root := by
  intro b acc xb xacc r hp hp' cs hb hB hacc ev hself hsub
  obtain ⟨n, ds, hn, hds⟩ := h hb hB hacc ev hself hsub
  exact ⟨n, ds, nestedWalk_le (storedView_le t E₀) B n 0 acc ds hn, hds⟩

/-- **The flattened family a family check compares is the one derived from the block over the
stored blocks**: `blockDerivedFlat_of_checks` with the reading of `nested_walk` over
`storedView`, at a block with `MembersStored`. -/
theorem storedDerivedFlat_of_checks {κ : _root_.Address → KKey} (hinj : Function.Injective κ)
    {t : Ix.Kernel.RoleTable} {B : _root_.Address} {off : Nat} {root : List (Call F)}
    (nested_walk : NestedWalkSpec κ (storedView t E₀) B root) (bd : Bounded root)
    (helim : BlockElim t E₀ B off) (hst : MembersStored E₀ B)
    {b : Bytes.Address} {es : List FlatEntry} {xb xflat r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (hroot : ∀ c ∈ cs, c ∈ root)
    (hb : Bytes.RepAddressRef addrTy h b xb) (hB : ixAddr b = B)
    (hes : RepList flatListEnum (FlatEntryRepExact κ) h es xflat)
    (horig : FlatOriginals t E₀ B off es)
    (ev : ObsFn W "KernelModeled::check_nested_aux" [xb, xflat] h r h' cs) :
    StoredDerivedFlat t E₀ B off es := by
  obtain ⟨n, hw⟩ := check_nested_aux_spec hinj nested_walk bd hroot hb hB hes ev
  obtain ⟨ms, hm, ho⟩ := horig
  refine ⟨helim, n, ?_⟩
  have hm' : (storedView t E₀).members B = some ms := by
    rw [storedView_members_of hst]; exact hm
  unfold derivedFlatAt
  simp only [hm', originals_storedView, ho]
  exact hw

/-- **The entries of the flattened family a family check compares differ.** -/
theorem flatDistinct_of_checks {κ : _root_.Address → KKey} (hinj : Function.Injective κ)
    {t : Ix.Kernel.RoleTable} {B : _root_.Address} {off : Nat} {root : List (Call F)}
    (nested_walk : NestedWalkSpec κ (storedView t E₀) B root) (bd : Bounded root)
    (helim : BlockElim t E₀ B off) (hst : MembersStored E₀ B)
    {b : Bytes.Address} {es : List FlatEntry} {xb xflat r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (hroot : ∀ c ∈ cs, c ∈ root)
    (hb : Bytes.RepAddressRef addrTy h b xb) (hB : ixAddr b = B)
    (hes : RepList flatListEnum (FlatEntryRepExact κ) h es xflat)
    (horig : FlatOriginals t E₀ B off es)
    (ev : ObsFn W "KernelModeled::check_nested_aux" [xb, xflat] h r h' cs) :
    FlatDistinct es :=
  (storedDerivedFlat_of_checks hinj nested_walk bd helim hst hroot hb hB hes horig
    ev).flatDistinct

open IxVM.Refinement.Typing.FamilyAlias in
/-- **The flattened family of an observed family check is derived from the block, and its
entries differ**: `blockDerivedFlat_of_checkFamily` with the reading of `nested_walk` over the
stored blocks (`nestedWalkSpec_storedView`), which gives `FlatDistinct` of the same entries. -/
theorem flatDistinct_of_call {t : Ix.Kernel.RoleTable}
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {κ : _root_.Address → KKey} (hinj : Function.Injective κ)
    (hka : ∀ a, keyAddr t (κ a) = some a)
    (hD : GuardDefnAnswers κ (defnValAt t E₀) calls)
    (hI : GuardIndAnswers κ (indTypeAt t E₀) calls)
    (nested_walk : NestedWalkSpec κ (storedView t E₀) B calls)
    (hbd : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hB : FamBlockRecord E₀ B cb ms) (hms_u64 : ms.size < UInt64.size)
    {rc xb xrb : SourceValue F} {h h' : Heap F} {cs : List (Call F)} (hsub : CallSub cs calls)
    (C : CheckFamilyChain rc xb xrb h h' cs) (X : CheckFamilyFlatChain C)
    {bB : Bytes.Address} (hbB : Bytes.RepAddressRef addrTy h bB xb) (hb : ixAddr bB = B)
    {es : List FlatEntry}
    (hes : RepList flatListEnum (FlatEntryRepExact κ) X.mFlat es X.flat)
    (horig : ∀ off : Nat, C.uo = .field (off : F) → BlockElim t E₀ B off →
      FlatOriginals t E₀ B off es) :
    ∃ off : Nat, C.uo = .field (off : F) ∧ BlockDerivedFlat t E₀ B off es ∧
      StoredDerivedFlat t E₀ B off es ∧ FlatDistinct es := by
  obtain ⟨off, huo, hder⟩ := blockDerivedFlat_of_checkFamily hinj hka hD hI nested_walk.ofStore
    hbd hS hB hms_u64 hsub C X hbB hb hes horig
  have hst : StoredDerivedFlat t E₀ B off es :=
    storedDerivedFlat_of_checks hinj nested_walk hbd hder.1
      (membersStored_of_famBlockRecord hB hms_u64)
      (fun c hc => hsub c (X.evNested.sub c hc))
      (Bytes.repAddressRef_heapMono₂ addrTy X.ext_in_mFlat hbB) hb hes
      (horig off huo hder.1) X.evNested.obs
  exact ⟨off, huo, hder, hst, hst.flatDistinct⟩

end Run

end IxVM.Refinement.Binding.FamilyRecon
