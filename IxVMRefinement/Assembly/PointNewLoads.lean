import IxVMRefinement.Assembly.PointRecord
import IxVMRefinement.Assembly.NativeBlockNewFacts

/-! # The new constants of a constructors-only install: their load facts

`PointInstall` (`PointRecord.lean`) states what the store reads of the constants a
constructors-only install puts in front of a prefix: the type former of each member of the block
at `B` (at the empty capability record) and its constructors. This file gives the facts about
those constants that `NewLoads` (`NativeBlockLoads.lean`) asks for, the analogues for a block of
any number of members of the facts `NativeBlockNewFacts.lean` gives for a block of one:

* `iprj_key_member`, `cprj_key_member`: a projection key of a hashed block that is the key of a
  member's former (of one of its constructors) is at that block, with the index the projection
  address reads (`toUInt64`); the records a hashed block's projection addresses hold are that
  block's projections (`HashedBlockProjectionsHeld`);
* `PointInstall.newInd`, `PointInstall.newCtor`: a new inductive is the stored former of a member,
  at the empty capability record; a new constructor is at the key of a constructor of a member;
* `PointInstall.famNew`: a family witnessed by a new constant at a hashed block is a member of the
  installed block;
* the fields `getCI`, `getCprj`, `getIprj`, `inductRecord`, `inductBlock`, `ctorIndRes` and
  `projTablesGuard` of `NewLoads` (`PointInstall.newGetCI`, …).

A projection address reads its indices as 64-bit numbers, so a key of the install names a member
up to that reading. The member a load reaches is the one at the read index, which is no larger
than the install's (`toNat_toUInt64_le`); every member of the block is an inductive, so the read
index is a member too.
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Indices read as 64-bit numbers -/

/-- The index a projection address reads is no larger than the index. -/
theorem toNat_toUInt64_le (k : Nat) : k.toUInt64.toNat ≤ k := by
  change (UInt64.ofNat k).toNat ≤ k
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_le _ _

/-- An index below `2 ^ 64` that a projection address reads as another index's is no larger than
that index. -/
theorem le_of_toUInt64_eq {i k : Nat} (hi : i < UInt64.size) (h : i.toUInt64 = k.toUInt64) :
    i ≤ k := by
  have e := congrArg UInt64.toNat h
  rw [toNat_toUInt64_of_lt hi] at e
  rw [e]
  exact toNat_toUInt64_le k

/-- The member projection address reads its index as a 64-bit number. -/
theorem iprjAddr_congr {b : _root_.Address} {i k : Nat} (h : i.toUInt64 = k.toUInt64) :
    Core.iprjAddr b i = Core.iprjAddr b k := by
  unfold Core.iprjAddr
  rw [h]

/-- The constructor projection address reads its indices as 64-bit numbers. -/
theorem cprjAddr_congr {b : _root_.Address} {i k j j' : Nat} (h : i.toUInt64 = k.toUInt64)
    (h' : j.toUInt64 = j'.toUInt64) : Core.cprjAddr b i j = Core.cprjAddr b k j' := by
  unfold Core.cprjAddr
  rw [h, h']

theorem toUInt64_toNat_toUInt64 (k : Nat) : (k.toUInt64.toNat).toUInt64 = k.toUInt64 :=
  UInt64.ofNat_toNat

theorem iprjAddr_toNat (b : _root_.Address) (k : Nat) :
    Core.iprjAddr b k.toUInt64.toNat = Core.iprjAddr b k :=
  iprjAddr_congr (toUInt64_toNat_toUInt64 k)

theorem cprjAddr_toNat (b : _root_.Address) (k j : Nat) :
    Core.cprjAddr b k.toUInt64.toNat j.toUInt64.toNat = Core.cprjAddr b k j :=
  cprjAddr_congr (toUInt64_toNat_toUInt64 k) (toUInt64_toNat_toUInt64 j)

/-! ## Two address facts -/

/-- **A member key of a hashed block that is the key of member `k`'s former is at the block of the
former**, with the index the projection address reads: the store holds member `k`'s projection at
its address, and the records a hashed block's projection addresses hold are its own. -/
theorem iprj_key_member {t : Ix.Kernel.RoleTable} (htwf : t.wf = true) {E : Ixon.Env}
    (hdec : L1.EnvDecoded E) (hP : HashedBlockProjectionsHeld E) {B b : _root_.Address}
    {k : Nat} {ind : Ixon.Inductive}
    (hproj : recordOf E (Core.iprjAddr B k) = some (memberProjection B k (.indc ind)))
    (hbh : Core.HashedBlockAt E b) {i : Nat}
    (hkey : Core.keyOf t (Core.iprjAddr b i) = Core.keyOf t (Core.iprjAddr B k)) :
    b = B ∧ i.toUInt64 = k.toUInt64 := by
  have hx : Core.iprjAddr b i = Core.iprjAddr B k := Core.keyOf_inj htwf hkey
  have hrec : Ix.Cert.recordAt E (Core.iprjAddr b i) =
      some (memberProjection B k (.indc ind)) := by
    rw [hx]
    exact recordAt_of_recordOf hdec hproj
  have hinfo := (hP b hbh).1 i _ hrec
  have h0 : (memberProjection B k (.indc ind)).info = .iPrj ⟨k.toUInt64, B⟩ := rfl
  rw [h0] at hinfo
  injection hinfo with hp
  injection hp with hidx hblk
  exact ⟨hblk.symm, hidx.symm⟩

/-- **A constructor key of a hashed block that is the key of constructor `j'` of member `k` is at
the block of that constructor**, with the indices the projection address reads. -/
theorem cprj_key_member {t : Ix.Kernel.RoleTable} (htwf : t.wf = true) {E : Ixon.Env}
    (hdec : L1.EnvDecoded E) (hP : HashedBlockProjectionsHeld E) {B b : _root_.Address}
    {k j' : Nat}
    (hproj : recordOf E (Core.cprjAddr B k j') = some (constructorProjection B k j'))
    (hbh : Core.HashedBlockAt E b) {i j : Nat}
    (hkey : Core.keyOf t (Core.cprjAddr b i j) = Core.keyOf t (Core.cprjAddr B k j')) :
    b = B ∧ i.toUInt64 = k.toUInt64 ∧ j.toUInt64 = j'.toUInt64 := by
  have hx : Core.cprjAddr b i j = Core.cprjAddr B k j' := Core.keyOf_inj htwf hkey
  have hrec : Ix.Cert.recordAt E (Core.cprjAddr b i j) = some (constructorProjection B k j') := by
    rw [hx]
    exact recordAt_of_recordOf hdec hproj
  have hinfo := (hP b hbh).2 i j _ hrec
  have h0 : (constructorProjection B k j').info = .cPrj ⟨k.toUInt64, j'.toUInt64, B⟩ := rfl
  rw [h0] at hinfo
  injection hinfo with hp
  injection hp with hidx hcidx hblk
  exact ⟨hblk.symm, hidx.symm, hcidx.symm⟩

/-! ## The install's new constants -/

section
variable {c : Core.Ctx} {new : List (ConstantInfo .anon)} {B : _root_.Address}
  {cb : Ixon.Constant} {ms : Array Ixon.MutConst}

/-- **Every index up to a member's is a member's**, an inductive: the block's members are all
inductive types. -/
theorem PointInstall.member_le (hI : PointInstall c new B cb ms) {k : Nat} {m : Ixon.MutConst}
    (hk : ms[k]? = some m) {i : Nat} (hle : i ≤ k) : ∃ ind, ms[i]? = some (.indc ind) := by
  have hlt : i < ms.size := Nat.lt_of_le_of_lt hle (Array.getElem?_eq_some_iff.mp hk).1
  obtain ⟨ind, hind⟩ := hI.inds i _ (Array.getElem?_eq_getElem hlt)
  exact ⟨ind, by rw [Array.getElem?_eq_getElem hlt, hind]⟩

/-- **The new inductive is a former**: an inductive the longer environment finds among the new
constants at an address's key is the stored former of member `k`, at the former's key and at the
empty capability record. -/
theorem PointInstall.newInd (hI : PointInstall c new B cb ms) {x : _root_.Address}
    {cv : ConstantVal .anon} {caps' : IndCaps .anon}
    (hf : (appCtx c new).env.find? ((appCtx c new).stored.κ x) = some (.indInfo cv caps'))
    (hm : ConstantInfo.indInfo cv caps' ∈ new) :
    ∃ (k : Nat) (ind : Ixon.Inductive), ms[k]? = some (.indc ind) ∧
      Core.keyOf c.t x = Core.keyOf c.t (Core.iprjAddr B k) ∧
      ∃ ty', cv = ⟨Core.keyOf c.t (Core.iprjAddr B k), List.range ind.lvls.toNat, ty'⟩ ∧
        caps' = {} := by
  have hn : cv.name = (appCtx c new).stored.κ x := Core.WhnfAux.name_of_find hf
  rcases hI.newName _ hm with ⟨k, ind, hk, hT⟩ | ⟨k, ind, j, hk, hj, hC⟩
  · obtain ⟨ty₀, ty', -, -, -, -, hfT⟩ := hI.former k ind hk
    have hT' : cv.name = Core.keyOf c.t (Core.iprjAddr B k) := hT
    have hκ : (appCtx c new).stored.κ x = Core.keyOf c.t (Core.iprjAddr B k) := hn.symm.trans hT'
    have hκ' := (appCtx c new).stored.key_eq (a := x) (by rw [hκ]; exact Core.Resolved.ne)
    refine ⟨k, ind, hk, hκ'.symm.trans hκ, ?_⟩
    rw [hκ, hfT] at hf
    injection hf with hf
    injection hf with h1 h2
    exact ⟨ty', h1.symm, h2.symm⟩
  · exfalso
    obtain ⟨ct, cty, cty', -, -, -, -, -, -, hfC⟩ := hI.ctor k ind hk j hj
    have hC' : cv.name = Core.keyOf c.t (Core.cprjAddr B k j) := hC
    rw [← hn, hC', hfC] at hf
    cases hf

/-- **The new constructor is the block's**: a constructor the longer environment finds among the
new constants at an address's key is at the key of constructor `j` of member `k`. -/
theorem PointInstall.newCtor (hI : PointInstall c new B cb ms) {x : _root_.Address}
    {cv : ConstantVal .anon} {nP nF : Nat}
    (hf : (appCtx c new).env.find? ((appCtx c new).stored.κ x) = some (.ctorInfo cv nP nF))
    (hm : ConstantInfo.ctorInfo cv nP nF ∈ new) :
    ∃ (k : Nat) (ind : Ixon.Inductive) (j : Nat), ms[k]? = some (.indc ind) ∧
      j < ind.ctors.size ∧ Core.keyOf c.t x = Core.keyOf c.t (Core.cprjAddr B k j) := by
  have hn : cv.name = (appCtx c new).stored.κ x := Core.WhnfAux.name_of_find hf
  rcases hI.newName _ hm with ⟨k, ind, hk, hT⟩ | ⟨k, ind, j, hk, hj, hC⟩
  · exfalso
    obtain ⟨ty₀, ty', -, -, -, -, hfT⟩ := hI.former k ind hk
    have hT' : cv.name = Core.keyOf c.t (Core.iprjAddr B k) := hT
    rw [← hn, hT', hfT] at hf
    cases hf
  · have hC' : cv.name = Core.keyOf c.t (Core.cprjAddr B k j) := hC
    have hκ : (appCtx c new).stored.κ x = Core.keyOf c.t (Core.cprjAddr B k j) := hn.symm.trans hC'
    have hκ' := (appCtx c new).stored.key_eq (a := x) (by rw [hκ]; exact Core.Resolved.ne)
    exact ⟨k, ind, j, hk, hj, hκ'.symm.trans hκ⟩

/-- **A family witnessed by a new constant at a hashed block is a member of the installed
block.** The index is below `2 ^ 64`: a projection address reads its index as a 64-bit number,
so the family at `i` and at `i + 2 ^ 64` are witnessed by the same constants. -/
theorem PointInstall.famNew (hI : PointInstall c new B cb ms) {b : _root_.Address} {i : Nat}
    (hbh : Core.HashedBlockAt c.E b) (hi : i < UInt64.size)
    (hfam : FamNew (appCtx c new).stored new b i) :
    b = B ∧ ∃ ind, ms[i]? = some (.indc ind) := by
  rcases hfam with ⟨cv, caps', hf, hm⟩ | ⟨j, cv, nP, nF, hf, hm⟩
  · obtain ⟨k, ind, hk, hkey, -⟩ := hI.newInd hf hm
    obtain ⟨hbB, hik⟩ :=
      iprj_key_member hI.wf hI.decoded hI.held (hI.formerRec k ind hk) hbh hkey
    exact ⟨hbB, hI.member_le hk (le_of_toUInt64_eq hi hik)⟩
  · obtain ⟨k, ind, j', hk, hj', hkey⟩ := hI.newCtor hf hm
    obtain ⟨hbB, hik, -⟩ :=
      cprj_key_member hI.wf hI.decoded hI.held (hI.ctorRec k ind hk j' hj') hbh hkey
    exact ⟨hbB, hI.member_le hk (le_of_toUInt64_eq hi hik)⟩

/-- The block's members are stored at the longer environment. -/
theorem PointInstall.blockStored (hI : PointInstall c new B cb ms) :
    LoadedReads.BlockStored c.t (appCtx c new).env B ms := by
  apply LoadedReads.blockStored_of_members
  intro k m hm
  obtain ⟨ind, rfl⟩ := hI.inds k m hm
  obtain ⟨ty₀, ty', -, -, -, -, hfT⟩ := hI.former k ind hm
  exact ⟨_, by rw [LoadedReads.memberAddr_indc]; exact hfT⟩

/-- The new keys at addresses are the formers' and the constructors'. -/
theorem PointInstall.newKey (hI : PointInstall c new B cb ms) {x : _root_.Address}
    (hn : ∃ cn ∈ new, cn.name = Core.keyOf c.t x) :
    (∃ (k : Nat) (ind : Ixon.Inductive), ms[k]? = some (.indc ind) ∧ x = Core.iprjAddr B k) ∨
      ∃ (k : Nat) (ind : Ixon.Inductive) (j : Nat), ms[k]? = some (.indc ind) ∧
        j < ind.ctors.size ∧ x = Core.cprjAddr B k j := by
  obtain ⟨cn, hcn, hname⟩ := hn
  rcases hI.newName cn hcn with ⟨k, ind, hk, hT⟩ | ⟨k, ind, j, hk, hj, hC⟩
  · exact Or.inl ⟨k, ind, hk, Core.keyOf_inj hI.wf (hname.symm.trans hT)⟩
  · exact Or.inr ⟨k, ind, j, hk, hj, Core.keyOf_inj hI.wf (hname.symm.trans hC)⟩

/-- **No new constant is a projection table**: every new constant is a former or a constructor,
found at its name. -/
theorem PointInstall.noTable (hI : PointInstall c new B cb ms) (tbl : Ix.Kernel.ProjTable .anon) :
    ConstantInfo.projInfo tbl ∉ new := by
  intro hm
  have hf := hI.newFind _ hm
  rcases hI.newName _ hm with ⟨k, ind, hk, hT⟩ | ⟨k, ind, j, hk, hj, hC⟩
  · obtain ⟨ty₀, ty', -, -, -, -, hfT⟩ := hI.former k ind hk
    rw [hT, hfT] at hf
    cases hf
  · obtain ⟨ct, cty, cty', -, -, -, -, -, -, hfC⟩ := hI.ctor k ind hk j hj
    rw [hC, hfC] at hf
    cases hf

end

end IxVM.Refinement.Typing
