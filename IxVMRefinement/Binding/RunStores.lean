import IxVMRefinement.Binding.WalkChecks
import IxVMRefinement.RoleVal.AxiomRefsLim
import IxVMRefinement.Assembly.TypingStore
import IxVMRefinement.StatementRel.RowsStore
import IxVMRefinement.StatementRel.StoreInhabit

/-! # The stores of a binding run, group by group

`GroupStoresOfRun calls` asks, of an accepted binding run, for a sequence of stores over the
run's records that starts at the committed basis rows and has every store clause of each
group's admission. This file defines the sequence and proves the clauses that read the store
alone; the clauses that read the walks are in `IxVMRefinement.Binding.StoreClausesWalk`.

* `recordsAt E S`: the records of `E` at the addresses of `S`, with every blob of `E`.
* `GroupReach t E₀ g a`: `a` is reached by the admission of group `g` over the run's records
  `E₀`: the bound record of a role of the group whose validation walks it, a reference the
  group's standard axiom uses, a reference a reached record uses, the block of a reached
  projection record, or a reference a proof in the evidence of a role of the group uses other
  than the role's own address (an equation theorem is walked with its closure, a certificate's
  references one by one; the proof's own record is not reached); a reference bound to a walked
  role in force at the group's validation limit is not followed (its own group reached it).
* `PayReach t E₀ Pay g a`: `a` is reached through the payload `Pay` of the group's family checks:
  an address the family check of a reached block names (its family record, an advice record, a
  container recursor), and from there used references not covered and projections' blocks. No
  walk of the group reaches these records; the facts the store's clauses need of them are
  premises (`PayloadFacts`, `IxVMRefinement.Binding.StoreClausesWalk`).
* `GroupAdds t E₀ Pay g a`: what the admission of group `g` adds: what its walk adds
  (`WalkAdds`: a reached address, a member's or a constructor's address of a reached block, or
  the address of the group's standard axiom) or what its payload adds (`PayAdds`: an address
  reached through the payload, or a member's or a constructor's address of a block reached so).
* `groupStore t E₀ Pay g`: the basis store at group 6, and from group 7 on the run's records at
  the basis rows' addresses and at what the groups from 6 below `g` add.
* `CollisionFreeRun calls E₀`: what the alternative without a collision gives of the run's
  store.
* `BasisRowsLoaded E₀`: the run's store holds the basis rows as the basis store does. It is a
  premise of the clauses here; its producer is the validation of the groups below 6 at a table
  that pins the prelude.

The clauses proved here, each for the store `groupStore t E₀ Pay g`: `groupStore_mono`,
`groupStore_monoBlobs`, `groupStore_loaded`, `groupStore_loadedBlobs`, `groupStore_hashed`,
`groupStore_committed`, `groupStore_zeroFree`, and the blob clause of the reading
(`groupStore_reads_blobs`).
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.StoreInhabit (basisStore)

/-! ## The records of a store at given addresses -/

/-- **The records of `E` at the addresses of `S`**, with every blob of `E`. -/
noncomputable def recordsAt (E : Ixon.Env) (S : _root_.Address → Prop) : Ixon.Env :=
  { consts := E.consts.filter fun x _ => @decide (S x) (Classical.propDecidable (S x))
    blobs := E.blobs }

theorem recordsAt_consts {E : Ixon.Env} {S : _root_.Address → Prop} {a : _root_.Address}
    {lc : Ixon.LazyConstant} :
    (recordsAt E S).consts.get? a = some lc ↔ S a ∧ E.consts.get? a = some lc := by
  show (E.consts.filter fun x _ => @decide (S x) (Classical.propDecidable (S x))).get? a =
    some lc ↔ _
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_filter', Std.HashMap.get?_eq_getElem?]
  cases hE : E.consts[a]? with
  | none => simp
  | some v =>
    by_cases hs : S a
    · simp [Option.filter, hs]
    · simp [Option.filter, hs]

theorem recordsAt_blobs (E : Ixon.Env) (S : _root_.Address → Prop) :
    (recordsAt E S).blobs = E.blobs := rfl

/-- **The record of a store that holds the entries of another at the addresses of `P`.** -/
theorem recordOf_restrict {R E : Ixon.Env} {a : _root_.Address} {P : Prop}
    (h : ∀ lc, R.consts.get? a = some lc ↔ P ∧ E.consts.get? a = some lc) (c : Ixon.Constant) :
    recordOf R a = some c ↔ P ∧ recordOf E a = some c := by
  unfold recordOf
  constructor
  · intro hr
    cases hR : R.consts.get? a with
    | none =>
      rw [hR] at hr
      exact absurd hr (by simp)
    | some lc =>
      obtain ⟨hp, hE⟩ := (h lc).mp hR
      rw [hR] at hr
      rw [hE]
      exact ⟨hp, hr⟩
  · rintro ⟨hp, hr⟩
    cases hE : E.consts.get? a with
    | none =>
      rw [hE] at hr
      exact absurd hr (by simp)
    | some lc =>
      rw [(h lc).mpr ⟨hp, hE⟩]
      rw [hE] at hr
      exact hr

/-! ## What a group's admission reaches and adds -/

/-- **A role-bound address already stored before group `g`**: a covered walked role
(`Claim.CoveredAt`), a walked anchor, standard axiom or quotient role in force at `valLimit g`,
or an operation of an earlier group (`groupOf r < g`). Stopping `GroupReach` and `PayReach`
here preserves the store `groupStore t E₀ Pay (g + 1)` verbatim (each disjunct is already in
`groupStore t E₀ Pay g`, which is `UsedClosed`) and aligns `GroupReach` with `op_order_scan`'s
stops in the well-founded block. -/
def AlreadyStoredRole (t : Ix.Kernel.RoleTable) (g : Nat) (x : _root_.Address) : Prop :=
  Claim.CoveredAt t (some (valLimit g)) x ∨
  (∃ r : Ix.Kernel.Role, t.addressOf? r = some x ∧
    Ix.SpecDigest.groupOf r < valLimit g ∧
    (RoleVal.anchorWalked r = true ∨ r ∈ standardAxioms ∨ RoleVal.isQuotRole r = true)) ∨
  (∃ r : Ix.Kernel.Role, t.addressOf? r = some x ∧
    RoleVal.roleSpecKindNat r = 2 ∧ Ix.SpecDigest.groupOf r < g)

theorem AlreadyStoredRole.of_covered {t : Ix.Kernel.RoleTable} {g : Nat} {x : _root_.Address}
    (h : Claim.CoveredAt t (some (valLimit g)) x) : AlreadyStoredRole t g x :=
  Or.inl h

theorem AlreadyStoredRole.not_covered {t : Ix.Kernel.RoleTable} {g : Nat} {x : _root_.Address}
    (h : ¬ AlreadyStoredRole t g x) : ¬ Claim.CoveredAt t (some (valLimit g)) x :=
  fun hc => h (Or.inl hc)

/-- **An address the admission of group `g` reaches** over the run's records `E₀` (module
docstring). -/
inductive GroupReach (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (g : Nat) :
    _root_.Address → Prop where
  | root {r : Ix.Kernel.Role} {a : _root_.Address} : r ∈ roleGroup g →
      (RoleVal.roleWalksBound r = true ∨ RoleVal.anchorWalked r = true) →
      t.addressOf? r = some a → GroupReach t E₀ g a
  | axiomRef {r : Ix.Kernel.Role} {a x : _root_.Address} : r ∈ roleGroup g →
      r ∈ standardAxioms → t.addressOf? r = some a → UsedRef E₀ a x →
      ¬ AlreadyStoredRole t g x → GroupReach t E₀ g x
  | ref {a x : _root_.Address} : GroupReach t E₀ g a → UsedRef E₀ a x →
      ¬ AlreadyStoredRole t g x → GroupReach t E₀ g x
  | owner {a : _root_.Address} {c : Ixon.Constant} : GroupReach t E₀ g a →
      recordOf E₀ a = some c → IsProj c → GroupReach t E₀ g (Ix.Cert.ownerOf a c)
  | evidenceRef {r : Ix.Kernel.Role} {arr : Array (Ix.Kernel.Evidence _root_.Address)}
      {thm x : _root_.Address} : r ∈ roleGroup g → (r, arr) ∈ t.evidence.toList →
      Ix.Kernel.Evidence.proof thm ∈ arr.toList → UsedRef E₀ thm x → t.addressOf? r ≠ some x →
      ¬ AlreadyStoredRole t g x → GroupReach t E₀ g x
  | eqnsProof {r : Ix.Kernel.Role} {arr : Array (Ix.Kernel.Evidence _root_.Address)}
      {thm : _root_.Address} : r ∈ roleGroup g → RoleVal.roleSpecKindNat r = 5 →
      (r, arr) ∈ t.evidence.toList → Ix.Kernel.Evidence.proof thm ∈ arr.toList →
      GroupReach t E₀ g thm
  | eqnsAnchor {r ar : Ix.Kernel.Role} {a : _root_.Address} : r ∈ roleGroup g →
      RoleVal.roleSpecKindNat r = 5 → ar ∈ RoleVal.eqnsAnchorsOf r →
      t.addressOf? ar = some a → GroupReach t E₀ g a

/-- **The payload of the groups' family checks**: `Pay g B a` says that the family check of the
block at `B` under the role context of group `g`'s validation names `a` (its family record, an
advice record or a container recursor). The run's instance is `runPayload`
(`IxVMRefinement.Binding.RunPayload`). -/
abbrev PayloadRel : Type := Nat → _root_.Address → _root_.Address → Prop

/-- **No payload.** -/
abbrev noPayload : PayloadRel := fun _ _ _ => False

/-- **An address the admission of group `g` reaches through its payload**: an address the family
check of a block the group reaches names (`payload`; `payloadOf` for a block reached so), and
from such an address, as the walk goes, a used reference that is not already stored and the block
of a projection record. Together with `GroupReach` it is the group's reach with the payload. -/
inductive PayReach (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (Pay : PayloadRel) (g : Nat) :
    _root_.Address → Prop where
  | payload {B a : _root_.Address} : GroupReach t E₀ g B → Pay g B a → PayReach t E₀ Pay g a
  | payloadOf {B a : _root_.Address} : PayReach t E₀ Pay g B → Pay g B a →
      PayReach t E₀ Pay g a
  | ref {a x : _root_.Address} : PayReach t E₀ Pay g a → UsedRef E₀ a x →
      ¬ AlreadyStoredRole t g x → PayReach t E₀ Pay g x
  | owner {a : _root_.Address} {c : Ixon.Constant} : PayReach t E₀ Pay g a →
      recordOf E₀ a = some c → IsProj c → PayReach t E₀ Pay g (Ix.Cert.ownerOf a c)

/-- **What the walk of group `g` adds**: a reached address, a member's or a constructor's address
of a reached block, or the address of the group's standard axiom. -/
def WalkAdds (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (g : Nat) (a : _root_.Address) : Prop :=
  GroupReach t E₀ g a ∨
    (∃ B c, GroupReach t E₀ g B ∧ recordOf E₀ B = some c ∧ IsBlock c ∧ ConstAddrOf B c a) ∨
    ∃ r ∈ roleGroup g, r ∈ standardAxioms ∧ t.addressOf? r = some a

/-- **What the payload of group `g` adds**: an address reached through the payload, or a
member's or a constructor's address of a block reached so. -/
def PayAdds (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (Pay : PayloadRel) (g : Nat)
    (a : _root_.Address) : Prop :=
  PayReach t E₀ Pay g a ∨
    ∃ B c, PayReach t E₀ Pay g B ∧ recordOf E₀ B = some c ∧ IsBlock c ∧ ConstAddrOf B c a

/-- **An address the admission of group `g` adds to the store**: what its walk adds, or what its
payload adds. -/
def GroupAdds (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (Pay : PayloadRel) (g : Nat)
    (a : _root_.Address) : Prop :=
  WalkAdds t E₀ g a ∨ PayAdds t E₀ Pay g a

/-- **Without a payload at the group, nothing is reached through it.** -/
theorem PayReach.false_of_empty {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {Pay : PayloadRel}
    {g : Nat} (hnp : ∀ B a, ¬ Pay g B a) {a : _root_.Address} (h : PayReach t E₀ Pay g a) :
    False := by
  induction h with
  | payload _ hp => exact hnp _ _ hp
  | payloadOf _ hp _ => exact hnp _ _ hp
  | ref _ _ _ ih => exact ih
  | owner _ _ _ ih => exact ih

theorem PayReach.none {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {g : Nat} {a : _root_.Address}
    (h : PayReach t E₀ noPayload g a) : False :=
  PayReach.false_of_empty (fun _ _ h => h) h

theorem PayAdds.false_of_empty {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {Pay : PayloadRel}
    {g : Nat} (hnp : ∀ B a, ¬ Pay g B a) {a : _root_.Address} (h : PayAdds t E₀ Pay g a) :
    False := by
  rcases h with h | ⟨_, _, h, _⟩
  · exact h.false_of_empty hnp
  · exact h.false_of_empty hnp

theorem GroupAdds.reach {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {Pay : PayloadRel} {g : Nat}
    {a : _root_.Address} (h : GroupReach t E₀ g a) : GroupAdds t E₀ Pay g a :=
  Or.inl (Or.inl h)

theorem GroupAdds.stdAxiom {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {Pay : PayloadRel}
    {g : Nat} {a : _root_.Address} {r : Ix.Kernel.Role} (hr : r ∈ roleGroup g)
    (hs : r ∈ standardAxioms) (had : t.addressOf? r = some a) : GroupAdds t E₀ Pay g a :=
  Or.inl (Or.inr (Or.inr ⟨r, hr, hs, had⟩))

theorem GroupAdds.payReach {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {Pay : PayloadRel}
    {g : Nat} {a : _root_.Address} (h : PayReach t E₀ Pay g a) : GroupAdds t E₀ Pay g a :=
  Or.inr (Or.inl h)

/-- **An address the store before group `g` holds a record at**: a basis row's address, or an
address a group from 6 below `g` adds. -/
def StoredBelow (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (Pay : PayloadRel) (g : Nat)
    (a : _root_.Address) : Prop :=
  (basisStore.consts.get? a).isSome = true ∨ ∃ k, 6 ≤ k ∧ k < g ∧ GroupAdds t E₀ Pay k a

/-- **The store before the admission of group `g`**: the basis store up to group 6; from group
7 on the run's records at the stored addresses, with every blob of the run. -/
noncomputable def groupStore (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (Pay : PayloadRel)
    (g : Nat) : Ixon.Env :=
  if g ≤ 6 then basisStore else recordsAt E₀ (StoredBelow t E₀ Pay g)

/-- **The run's store holds the basis rows** as the basis store holds them. -/
def BasisRowsLoaded (E₀ : Ixon.Env) : Prop :=
  ∀ a lc, basisStore.consts.get? a = some lc → E₀.consts.get? a = some lc

/-- **What the alternative without a collision gives of the run's store**: it is the run's one
store and holds every record the run hashed; a byte string the run hashed at a committed row's
address is that row's; and the run hashed nothing at the zero address. -/
structure CollisionFreeRun (calls : List (Call F)) (E₀ : Ixon.Env) : Prop where
  runStore : LoadedReads.RunStore calls E₀
  hashedStored : LoadedReads.HashedRecordsStored calls E₀
  committed : ∀ p ∈ committedRows, ∀ bytes, Hashed calls bytes →
    Address.blake3Pure bytes = p.1 → bytes = p.2
  noPadding : ∀ bytes, Hashed calls bytes →
    Address.blake3Pure bytes ≠ Ix.HostAdmission.Merkle.padding

/-- **A run that hashed no collision with the committed footprint has a collision-free
store.** -/
theorem collisionFreeRun_of_no_collision {V : View} {extra : List ByteArray}
    {calls : List (Call F)} {E₀ : Ixon.Env}
    (hextra : ∀ x ∈ committedFootprint, x ∈ extra) (hno : ¬ V.HashedCollision extra calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀) :
    CollisionFreeRun calls E₀ where
  runStore := hS
  hashedStored := hH
  committed := by
    intro p hp bytes hh hbl
    by_contra hne
    exact hno (Or.inl ⟨p.1, p.2, bytes,
      Or.inr (Or.inl ⟨hextra _ (committedRows_footprint hp),
        ClosedFacts.committedRows_hashed p hp⟩), hh, hne, hbl⟩)
  noPadding := by
    intro bytes hh hbl
    exact hno (Or.inr (Or.inr ⟨bytes, Or.inr hh, hbl⟩))

section Store

variable {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {Pay : PayloadRel}

theorem groupStore_six : groupStore t E₀ Pay 6 = basisStore := by
  unfold groupStore
  rw [ite_eq_left (Nat.le_refl 6)]

theorem groupStore_above {g : Nat} (hg : 6 < g) :
    groupStore t E₀ Pay g = recordsAt E₀ (StoredBelow t E₀ Pay g) := by
  unfold groupStore
  rw [ite_eq_right (Nat.not_le_of_lt hg)]

/-- **The store at group 6 is the basis store**, entry by entry. -/
theorem groupStore_basis_consts (x : _root_.Address) :
    (groupStore t E₀ Pay 6).consts.get? x = basisStore.consts.get? x := by
  rw [groupStore_six]

theorem groupStore_basis_blobs (x : _root_.Address) :
    (groupStore t E₀ Pay 6).blobs.get? x = basisStore.blobs.get? x := by
  rw [groupStore_six]

theorem groupStore_blobs {g : Nat} (hg : 6 < g) : (groupStore t E₀ Pay g).blobs = E₀.blobs := by
  rw [groupStore_above hg]
  rfl

/-- **An entry of the store before group `g`** is the run's entry at a stored address. -/
theorem groupStore_consts (hb : BasisRowsLoaded E₀) {g : Nat} (hg : 6 ≤ g)
    {a : _root_.Address} {lc : Ixon.LazyConstant} :
    (groupStore t E₀ Pay g).consts.get? a = some lc ↔
      StoredBelow t E₀ Pay g a ∧ E₀.consts.get? a = some lc := by
  by_cases h6 : g = 6
  · subst h6
    rw [groupStore_six]
    constructor
    · intro h
      refine ⟨Or.inl ?_, hb a lc h⟩
      rw [h]
      rfl
    · rintro ⟨hs, hE⟩
      rcases hs with hs | ⟨k, hk6, hk, -⟩
      · obtain ⟨lc', hlc'⟩ := Option.isSome_iff_exists.mp hs
        have hE' := hb a lc' hlc'
        rw [hE] at hE'
        rw [hlc']
        exact hE'.symm
      · omega
  · rw [groupStore_above (by omega)]
    exact recordsAt_consts

/-- **A record of the store before group `g`** is the run's record at a stored address. -/
theorem groupStore_recordOf (hb : BasisRowsLoaded E₀) {g : Nat} (hg : 6 ≤ g)
    {a : _root_.Address} {c : Ixon.Constant} :
    recordOf (groupStore t E₀ Pay g) a = some c ↔
      StoredBelow t E₀ Pay g a ∧ recordOf E₀ a = some c :=
  recordOf_restrict (fun lc => groupStore_consts hb hg) c

theorem storedBelow_succ {g : Nat} {a : _root_.Address} (h : StoredBelow t E₀ Pay g a) :
    StoredBelow t E₀ Pay (g + 1) a := by
  rcases h with h | ⟨k, hk6, hk, hadd⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, hk6, by omega, hadd⟩

theorem storedBelow_of_adds {g : Nat} (hg : 6 ≤ g) {a : _root_.Address}
    (h : GroupAdds t E₀ Pay g a) : StoredBelow t E₀ Pay (g + 1) a :=
  Or.inr ⟨g, hg, Nat.lt_succ_self g, h⟩

theorem storedBelow_le {g g' : Nat} (hle : g ≤ g') {a : _root_.Address}
    (h : StoredBelow t E₀ Pay g a) : StoredBelow t E₀ Pay g' a := by
  rcases h with h | ⟨k, hk6, hk, hadd⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, hk6, by omega, hadd⟩

/-- **A record new in group `g`'s admission** is a record of the run at an address the group
adds and no earlier store held. -/
theorem new_groupStore (hb : BasisRowsLoaded E₀) {g : Nat} (hg : 6 ≤ g) {a : _root_.Address}
    (h : New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) a) :
    ∃ c, recordOf E₀ a = some c ∧ recordOf (groupStore t E₀ Pay (g + 1)) a = some c ∧
      GroupAdds t E₀ Pay g a ∧ ¬ StoredBelow t E₀ Pay g a := by
  obtain ⟨hs, hn⟩ := h
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨hst, hE⟩ := (groupStore_recordOf hb (Nat.le_succ_of_le hg)).mp hc
  have hnot : ¬ StoredBelow t E₀ Pay g a := by
    intro hsb
    have hrec := (groupStore_recordOf hb hg).mpr ⟨hsb, hE⟩
    rw [hn] at hrec
    cases hrec
  refine ⟨c, hE, hc, ?_, hnot⟩
  rcases hst with hbas | ⟨k, hk6, hk, hadd⟩
  · exact absurd (Or.inl hbas) hnot
  · by_cases hkg : k = g
    · subst hkg
      exact hadd
    · exact absurd (Or.inr ⟨k, hk6, by omega, hadd⟩) hnot

/-! ## The clauses that read the store alone -/

/-- **`Admits.mono`**: the store after a group holds what the store before it holds. -/
theorem groupStore_mono (hb : BasisRowsLoaded E₀) {g : Nat} (hg : 6 ≤ g) :
    ∀ a lc, (groupStore t E₀ Pay g).consts.get? a = some lc →
      (groupStore t E₀ Pay (g + 1)).consts.get? a = some lc := by
  intro a lc h
  obtain ⟨hs, hE⟩ := (groupStore_consts hb hg).mp h
  exact (groupStore_consts hb (Nat.le_succ_of_le hg)).mpr ⟨storedBelow_succ hs, hE⟩

/-- **`Admits.monoBlobs`**. -/
theorem groupStore_monoBlobs {g : Nat} (hg : 6 ≤ g) :
    ∀ a b, (groupStore t E₀ Pay g).blobs.get? a = some b →
      (groupStore t E₀ Pay (g + 1)).blobs.get? a = some b := by
  intro a b h
  by_cases h6 : g = 6
  · subst h6
    rw [groupStore_six] at h
    have h' : basisStore.blobs.get? a = none :=
      RowsStore.blobs_none (rows := StoreInhabit.basisRows) a
    rw [h'] at h
    cases h
  · rw [groupStore_blobs (by omega)] at h
    rw [groupStore_blobs (by omega)]
    exact h

/-- **`Admits.loaded`**: a store of the sequence holds records the run loaded. -/
theorem groupStore_loaded (hb : BasisRowsLoaded E₀) {g : Nat} (hg : 6 ≤ g) :
    ∀ a lc, (groupStore t E₀ Pay g).consts.get? a = some lc → E₀.consts.get? a = some lc :=
  fun a lc h => ((groupStore_consts hb hg).mp h).2

/-- **`Admits.loadedBlobs`**. -/
theorem groupStore_loadedBlobs {g : Nat} (hg : 6 < g) :
    ∀ a b, (groupStore t E₀ Pay g).blobs.get? a = some b → E₀.blobs.get? a = some b := by
  intro a b h
  rw [groupStore_blobs hg] at h
  exact h

/-- **The blob clause of `AdmitsReads`**: a store from group 7 on holds every blob of the
run. -/
theorem groupStore_reads_blobs {g : Nat} (hg : 6 < g) :
    ∀ x b, E₀.blobs.get? x = some b → (groupStore t E₀ Pay g).blobs.get? x = some b := by
  intro x b h
  rw [groupStore_blobs hg]
  exact h

/-- **`Admits.hashed`**: a store of the sequence is stored under the hashes of its bytes. -/
theorem groupStore_hashed {calls : List (Call F)} (hS : LoadedReads.RunStore calls E₀)
    (hb : BasisRowsLoaded E₀) {g : Nat} (hg : 6 < g) : EnvSelfHashed (groupStore t E₀ Pay g) := by
  unfold EnvSelfHashed
  constructor
  · intro a lc h
    exact (hS.loaded.1 a lc (groupStore_loaded hb (Nat.le_of_lt hg) a lc h)).2
  · intro a bytes h
    rw [groupStore_blobs hg] at h
    exact (hS.loaded.2 a bytes h).2

/-- **`Admits.committed`**: a store of the sequence agrees with the committed prelude. -/
theorem groupStore_committed {calls : List (Call F)} (hC : CollisionFreeRun calls E₀)
    (hb : BasisRowsLoaded E₀) {g : Nat} (hg : 6 ≤ g) : AgreesCommitted (groupStore t E₀ Pay g) := by
  unfold AgreesCommitted
  intro p hp lc h
  obtain ⟨hh, hbl⟩ := hC.runStore.loaded.1 p.1 lc (groupStore_loaded hb hg p.1 lc h)
  exact hC.committed p hp lc.rawBytes hh hbl

/-- **`Admits.zeroFree`**: a store of the sequence holds nothing at the zero address. -/
theorem groupStore_zeroFree {calls : List (Call F)} (hC : CollisionFreeRun calls E₀)
    (hb : BasisRowsLoaded E₀) {g : Nat} (hg : 6 < g) :
    (groupStore t E₀ Pay g).consts.get? Ix.HostAdmission.Merkle.padding = none ∧
      (groupStore t E₀ Pay g).blobs.get? Ix.HostAdmission.Merkle.padding = none := by
  constructor
  · cases h : (groupStore t E₀ Pay g).consts.get? Ix.HostAdmission.Merkle.padding with
    | none => rfl
    | some lc =>
      obtain ⟨hh, hbl⟩ := hC.runStore.loaded.1 _ lc
        (groupStore_loaded hb (Nat.le_of_lt hg) _ lc h)
      exact absurd hbl (hC.noPadding _ hh)
  · rw [groupStore_blobs hg]
    cases h : E₀.blobs.get? Ix.HostAdmission.Merkle.padding with
    | none => rfl
    | some bytes =>
      obtain ⟨hh, hbl⟩ := hC.runStore.loaded.2 _ bytes h
      exact absurd hbl (hC.noPadding _ hh)

end Store

end IxVM.Refinement.Binding
