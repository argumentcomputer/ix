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
  `projCtorTele` of `NewLoads` (`PointInstall.newGetCI`, …).

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
    (hk : ms[k]? = some m) {i : Nat} (hle : i ≤ k) : ∃ ind : Ixon.Inductive, ms[i]? = some (.indc ind) := by
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
    b = B ∧ ∃ ind : Ixon.Inductive, ms[i]? = some (.indc ind) := by
  rcases hfam with ⟨cv, caps', hf, hm⟩ | ⟨j, cv, nP, nF, hf, hm⟩
  · obtain ⟨k, ind, hk, hkey, -⟩ := hI.newInd hf hm
    obtain ⟨hbB, hik⟩ :=
      iprj_key_member hI.wf hI.decoded hI.held (hI.formerRec k ind hk) hbh hkey
    exact ⟨hbB, hI.member_le hk (le_of_toUInt64_eq hi hik)⟩
  · obtain ⟨k, ind, j', hk, hj', hkey⟩ := hI.newCtor hf hm
    obtain ⟨hbB, hik, -⟩ :=
      cprj_key_member hI.wf hI.decoded hI.held (hI.ctorRec k ind hk j' hj') hbh hkey
    exact ⟨hbB, hI.member_le hk (le_of_toUInt64_eq hi hik)⟩

/-- `PointInstall.famNew` at any index: the family is at the installed block, at an index the
projection address reads as a member's. -/
theorem PointInstall.famNew_toUInt64 (hI : PointInstall c new B cb ms) {b : _root_.Address}
    {i : Nat} (hbh : Core.HashedBlockAt c.E b) (hfam : FamNew (appCtx c new).stored new b i) :
    b = B ∧ ∃ (k : Nat) (ind : Ixon.Inductive), ms[k]? = some (.indc ind) ∧
      i.toUInt64 = k.toUInt64 := by
  rcases hfam with ⟨cv, caps', hf, hm⟩ | ⟨j, cv, nP, nF, hf, hm⟩
  · obtain ⟨k, ind, hk, hkey, -⟩ := hI.newInd hf hm
    obtain ⟨hbB, hik⟩ :=
      iprj_key_member hI.wf hI.decoded hI.held (hI.formerRec k ind hk) hbh hkey
    exact ⟨hbB, k, ind, hk, hik⟩
  · obtain ⟨k, ind, j', hk, hj', hkey⟩ := hI.newCtor hf hm
    obtain ⟨hbB, hik, -⟩ :=
      cprj_key_member hI.wf hI.decoded hI.held (hI.ctorRec k ind hk j' hj') hbh hkey
    exact ⟨hbB, k, ind, hk, hik⟩

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

/-! ## The loads of the new constants -/

/-- **A load of a constructor-projection record names a constructor slot of its block**: the
circuit loads the member at the record's member index and its constructor at the record's
constructor index. -/
theorem get_ci_cprj_slot {E : Ixon.Env} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbound : Bounded cs)
    {a : Bytes.Address} {addr ptr : SourceValue F} {h h' : Heap F}
    (ha : Bytes.RepAddressRef Core.addrTy h a addr)
    (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs) {c₀ cb : Ixon.Constant}
    {p : Ixon.ConstructorProj} {ms : Array Ixon.MutConst}
    (hrec : recordOf E (Core.ixAddr a) = some c₀) (hinfo : c₀.info = .cPrj p)
    (hblock : recordOf E p.block = some cb) (hmuts : cb.info = .muts ms) :
    ∃ (ind : Ixon.Inductive) (ct : Ixon.Constructor), ms[p.idx.toNat]? = some (.indc ind) ∧
      ind.ctors[p.cidx.toNat]? = some ct := by
  obtain ⟨rawBytes, c', hh, haddr, hex, htv, hres⟩ := L1.get_ci_block_trace_spec hbound ha ev
  obtain ⟨lc, hget, hdec⟩ := LoadedReads.recordOf_inv hrec
  have hb : rawBytes = lc.rawBytes := Core.load_escape hget hnc rawBytes hh haddr
  have hc : c₀ = c' := by
    rw [hb, hdec] at hex
    exact Except.ok.inj hex
  subst hc
  unfold L1.GetCIBlockTraceResult at hres
  rw [hinfo] at hres
  obtain ⟨-, -, blkBytes, cb', ms', ind', ct', blobs, tree, plan, v, hhB, haB, hexB, hcb, hms,
    hcts, -⟩ := hres
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hblock
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hnc blkBytes hhB haB
  have hcB : cb = cb' := by
    rw [hbB, hdecB] at hexB
    exact Except.ok.inj hexB
  subst hcB
  have hmsEq : ms = ms' := Ixon.ConstantInfo.muts.inj (hmuts.symm.trans hcb)
  subst hmsEq
  refine ⟨ind', ct', ?_, ?_⟩
  · rw [← Array.getElem?_toList]
    exact hms
  · rw [← Array.getElem?_toList]
    exact hcts

section
variable {c : Core.Ctx} {new : List (ConstantInfo .anon)} {B : _root_.Address}
  {cb : Ixon.Constant} {ms : Array Ixon.MutConst}

/-- **`NewLoads.getCI`.** A load at the key of a new constant loads the projection record the
store holds there; it represents the former (at the empty capability record) or the
constructor stored at that key. -/
theorem PointInstall.newGetCI (hI : PointInstall c new B cb ms) :
    ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address),
      ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs → Core.Good (appCtx c new) cs →
      Bytes.RepAddressRef Core.addrTy h a addr →
      (∃ cn ∈ new, cn.name = Core.keyOf c.t (Core.ixAddr a)) →
        ∃ ci, (appCtx c new).env.find? ((appCtx c new).stored.κ (Core.ixAddr a)) = some ci ∧
          Core.CIPtrRep (appCtx c new).stored.κ h' ptr ci := by
  intro addr ptr h h' cs a ev good ha hn
  rcases hI.newKey hn with ⟨k₀, ind₀, hk₀, hx⟩ | ⟨k₀, ind₀, j₀, hk₀, hj₀, hx⟩
  · -- the former of member `k₀`, loaded as the member at the index the record reads
    obtain ⟨ind, hk⟩ := hI.member_le hk₀ (toNat_toUInt64_le k₀)
    obtain ⟨ty₀, ty', hty, hlbb, hdef, hcan, hfT⟩ := hI.former _ ind hk
    have hrecA : recordOf c.E (Core.ixAddr a) = some (memberProjection B k₀ (.indc ind₀)) := by
      rw [hx]
      exact hI.formerRec k₀ ind₀ hk₀
    obtain ⟨-, ty'', hcan', -, -, hrep⟩ := LoadedReads.get_ci_iprj_canon
      (p := ⟨k₀.toUInt64, B⟩) hI.check good.1 good.2 ha ev hrecA rfl hI.block hI.muts hk hty
      hlbb hdef
    have hcan'' : LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
        ((L1.mutsRootOffset ms.toList k₀.toUInt64.toNat : Nat) : F) ind.typ ty₀ = some ty'' :=
      hcan'
    have e : ty'' = ty' := Option.some.inj (hcan''.symm.trans hcan)
    subst e
    have hxk : Core.ixAddr a = Core.iprjAddr B k₀.toUInt64.toNat :=
      hx.trans (iprjAddr_toNat B k₀).symm
    have hfA : (appCtx c new).env.find? (Core.keyOf c.t (Core.ixAddr a)) =
        some (.indInfo ⟨Core.keyOf c.t (Core.ixAddr a), List.range ind.lvls.toNat, ty''⟩ {}) := by
      rw [hxk]
      exact hfT
    refine ⟨_, ?_, hrep (appCtx c new).env c.lim hI.used hI.blockStored {}⟩
    rw [appCtx_key_of_find hfA]
    exact hfA
  · -- constructor `j₀` of member `k₀`, loaded at the slot the record reads
    have hrecA : recordOf c.E (Core.ixAddr a) = some (constructorProjection B k₀ j₀) := by
      rw [hx]
      exact hI.ctorRec k₀ ind₀ hk₀ j₀ hj₀
    obtain ⟨ind, ct, hk', hct'⟩ := get_ci_cprj_slot (p := ⟨k₀.toUInt64, j₀.toUInt64, B⟩) good.1
      good.2 ha ev hrecA rfl hI.block hI.muts
    have hk : ms[k₀.toUInt64.toNat]? = some (.indc ind) := hk'
    have hct : ind.ctors[j₀.toUInt64.toNat]? = some ct := hct'
    have hj : j₀.toUInt64.toNat < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hct).1
    obtain ⟨ct₁, cty, cty', hct₁, hcidx, hty, hlbb, hdef, hcan, hfC⟩ := hI.ctor _ ind hk _ hj
    have e₁ : ct₁ = ct := Option.some.inj (hct₁.symm.trans hct)
    subst e₁
    obtain ⟨-, ty'', hcan', -, -, hrep⟩ := LoadedReads.get_ci_cprj_canon
      (p := ⟨k₀.toUInt64, j₀.toUInt64, B⟩) (ct := ct₁) hI.check good.1 good.2 ha ev hrecA rfl
      hI.block hI.muts hk hct₁ hcidx hty hlbb hdef
    have hcan'' : LoadedReads.canonAnn cb (List.range ct₁.lvls.toNat)
        (((L1.mutsRootOffset ms.toList k₀.toUInt64.toNat : Nat) : F) + 1 +
          ((j₀.toUInt64.toNat : Nat) : F)) ct₁.typ cty = some ty'' := hcan'
    have e : ty'' = cty' := Option.some.inj (hcan''.symm.trans hcan)
    subst e
    have hxk : Core.ixAddr a = Core.cprjAddr B k₀.toUInt64.toNat j₀.toUInt64.toNat :=
      hx.trans (cprjAddr_toNat B k₀ j₀).symm
    have hfA : (appCtx c new).env.find? (Core.keyOf c.t (Core.ixAddr a)) =
        some (.ctorInfo ⟨Core.keyOf c.t (Core.ixAddr a), List.range ct₁.lvls.toNat, ty''⟩
          ct₁.params.toNat ct₁.fields.toNat) := by
      rw [hxk]
      exact hfC
    refine ⟨_, ?_, hrep (appCtx c new).env c.lim hI.used hI.blockStored ⟨_, hfA⟩⟩
    rw [appCtx_key_of_find hfA]
    exact hfA

/-- **`NewLoads.getIprj`.** -/
theorem PointInstall.newGetIprj (hI : PointInstall c new B cb ms) :
    ∀ (bp ptr : SourceValue F) (i : F) (h h' : Heap F) (cs : List (Call F)) (b : Bytes.Address),
      ObsFn Core.W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' cs →
      FamNew (appCtx c new).stored new (Core.ixAddr b) (ZMod.val i) →
      Core.Good (appCtx c new) cs → Bytes.RepAddressRef Core.addrTy h b bp →
        ∃ ci, (appCtx c new).env.find?
            ((appCtx c new).stored.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i))) = some ci ∧
          Core.CIPtrRep (appCtx c new).stored.κ h' ptr ci := by
  intro bp ptr i h h' cs b ev hfam good hb
  have hbh := L1.hashedBlockAt_of_get_ci_iprj (c := appCtx c new) good hb ev
  obtain ⟨hbB, ind, hmem⟩ := hI.famNew hbh (val_lt_uint64 i) hfam
  obtain ⟨ty₀, ty', hty, hlbb, hdef, hcan, hfT⟩ := hI.former (ZMod.val i) ind hmem
  have hblock' : recordOf c.E (Core.ixAddr b) = some cb := by
    rw [hbB]
    exact hI.block
  have hty' : (exprReader c.t (fun x => c.E.blobs.get? x) cb id
      (blockSelf c.t (Core.ixAddr b) ms)).read ind.typ = .ok ty₀ := by
    rw [hbB]
    exact hty
  obtain ⟨ty'', hcan', -, -, hrep⟩ := LoadedReads.get_ci_iprj_load_canon hI.check good.1 good.2
    hb ev hblock' hI.muts hmem hty' hlbb hdef
  have hcan'' : LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
      ((L1.mutsRootOffset ms.toList (ZMod.val i) : Nat) : F) ind.typ ty₀ = some ty'' := hcan'
  have e : ty'' = ty' := Option.some.inj (hcan''.symm.trans hcan)
  subst e
  have hbs : LoadedReads.BlockStored c.t (appCtx c new).env (Core.ixAddr b) ms := by
    rw [hbB]
    exact hI.blockStored
  have hfA : (appCtx c new).env.find?
      (Core.keyOf c.t (Core.iprjAddr (Core.ixAddr b) (ZMod.val i))) =
      some (.indInfo ⟨Core.keyOf c.t (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)),
        List.range ind.lvls.toNat, ty''⟩ {}) := by
    rw [hbB]
    exact hfT
  refine ⟨_, ?_, hrep (appCtx c new).env c.lim hI.used hbs {}⟩
  rw [appCtx_key_of_find hfA]
  exact hfA

/-- **`NewLoads.getCprj`.** -/
theorem PointInstall.newGetCprj (hI : PointInstall c new B cb ms) :
    ∀ (bp ptr : SourceValue F) (i j : F) (h h' : Heap F) (cs : List (Call F)) (b : Bytes.Address),
      ObsFn Core.W "Ingress::get_ci_cprj" [bp, .field i, .field j] h ptr h' cs →
      FamNew (appCtx c new).stored new (Core.ixAddr b) (ZMod.val i) →
      Core.Good (appCtx c new) cs → Bytes.RepAddressRef Core.addrTy h b bp →
        (∃ ci₀, Core.CIPtrRep (appCtx c new).stored.κ h' ptr ci₀) ∧
        ∀ cv nP nF, (appCtx c new).env.find? ((appCtx c new).stored.κ
            (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) (ZMod.val j))) =
            some (.ctorInfo cv nP nF) →
          Core.CIPtrRep (appCtx c new).stored.κ h' ptr (.ctorInfo cv nP nF) := by
  intro bp ptr i j h h' cs b ev hfam good hb
  have hbh := L1.hashedBlockAt_of_get_ci_cprj (c := appCtx c new) good hb ev
  obtain ⟨hbB, ind, hmem⟩ := hI.famNew hbh (val_lt_uint64 i) hfam
  have hblock' : recordOf c.E (Core.ixAddr b) = some cb := by
    rw [hbB]
    exact hI.block
  -- the slot exists in the record
  obtain ⟨-, -, -, blkBytes, cb', ms', ind', ct', blobs, v, hhB, haB, hexB, -, hcb, hms, hcts,
    -⟩ := L1.get_ci_cprj_origin_spec good.2 hb ev
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hblock'
  have hbB' : blkBytes = lcB.rawBytes := Core.load_escape hgetB good.1 blkBytes hhB haB
  have hcB : cb = cb' := by
    rw [hbB', hdecB] at hexB
    exact Except.ok.inj hexB
  subst hcB
  have hmsEq : ms = ms' := Ixon.ConstantInfo.muts.inj (hI.muts.symm.trans hcb)
  subst hmsEq
  have hiEq : ind = ind' := by
    have hms0 : ms[ZMod.val i]? = some (.indc ind') := by
      rw [← Array.getElem?_toList]
      exact hms
    exact Ixon.MutConst.indc.inj (Option.some.inj (hmem.symm.trans hms0))
  subst hiEq
  have hct : ind.ctors[ZMod.val j]? = some ct' := by
    rw [← Array.getElem?_toList]
    exact hcts
  have hjs : ZMod.val j < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hct).1
  obtain ⟨ct, cty, cty', hct₀, hcidx, hty, hlbb, hdef, hcan, hfC⟩ :=
    hI.ctor (ZMod.val i) ind hmem (ZMod.val j) hjs
  have hty' : (exprReader c.t (fun x => c.E.blobs.get? x) cb id
      (blockSelf c.t (Core.ixAddr b) ms)).read ct.typ = .ok cty := by
    rw [hbB]
    exact hty
  obtain ⟨ty'', hcan', -, -, hrep⟩ := LoadedReads.get_ci_cprj_load_canon hI.check good.1 good.2
    hb ev hblock' hI.muts hmem hct₀ hcidx hty' hlbb hdef
  have hcan'' : LoadedReads.canonAnn cb (List.range ct.lvls.toNat)
      (((L1.mutsRootOffset ms.toList (ZMod.val i) : Nat) : F) + 1 + ((ZMod.val j : Nat) : F))
      ct.typ cty = some ty'' := hcan'
  have e : ty'' = cty' := Option.some.inj (hcan''.symm.trans hcan)
  subst e
  have hfA : (appCtx c new).env.find?
      (Core.keyOf c.t (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) (ZMod.val j))) =
      some (.ctorInfo ⟨Core.keyOf c.t (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) (ZMod.val j)),
        List.range ct.lvls.toNat, ty''⟩ ct.params.toNat ct.fields.toNat) := by
    rw [hbB]
    exact hfC
  have hbs : LoadedReads.BlockStored c.t (appCtx c new).env (Core.ixAddr b) ms := by
    rw [hbB]
    exact hI.blockStored
  have hr := hrep (appCtx c new).env c.lim hI.used hbs ⟨_, hfA⟩
  refine ⟨⟨_, hr⟩, fun cv nP nF hf => ?_⟩
  rw [appCtx_key_of_find hfA, hfA] at hf
  rw [← Option.some.inj hf]
  exact hr

/-- **`NewLoads.inductRecord`.** -/
theorem PointInstall.newInductRecord (hI : PointInstall c new B cb ms) :
    ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address)
      (nl ty np ni nc u blk idx : SourceValue F),
      ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs →
      (∃ cn ∈ new, cn.name = Core.keyOf c.t (Core.ixAddr a)) → Core.Good (appCtx c new) cs →
      Bytes.RepAddressRef Core.addrTy h a addr →
      loadValue h' ptr = .ok (.construct Core.kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]) →
      ∃ (cm : Ixon.Constant) (b : Bytes.Address) (i : F),
        Ix.Cert.recordAt c.E (Core.ixAddr a) = some cm ∧ Bytes.RepAddressRef Core.addrTy h' b blk ∧
        idx = .field i ∧ cm.info = .iPrj ⟨(ZMod.val i).toUInt64, Core.ixAddr b⟩ := by
  intro addr ptr h h' cs a nl ty np ni nc u blk idx ev hn good ha hld
  obtain ⟨c₀, hrec⟩ : ∃ c₀, recordOf c.E (Core.ixAddr a) = some c₀ := by
    rcases hI.newKey hn with ⟨k, ind, hk, hx⟩ | ⟨k, ind, j, hk, hj, hx⟩
    · exact ⟨_, by rw [hx]; exact hI.formerRec k ind hk⟩
    · exact ⟨_, by rw [hx]; exact hI.ctorRec k ind hk j hj⟩
  obtain ⟨b, i, hrecA, hb, hidx, hinfo⟩ :=
    get_ci_induct_record hI.decoded good.1 good.2 ev ha hld hrec
  exact ⟨c₀, b, i, hrecA, hb, hidx, hinfo⟩

/-- **`NewLoads.inductBlock`.** -/
theorem PointInstall.newInductBlock (hI : PointInstall c new B cb ms) :
    ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a b : Bytes.Address)
      (nl ty np ni nc u blk : SourceValue F) (i : F),
      ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs →
      (∃ cn ∈ new, cn.name = Core.keyOf c.t (Core.ixAddr a)) → Core.Good (appCtx c new) cs →
      Bytes.RepAddressRef Core.addrTy h a addr →
      loadValue h' ptr =
        .ok (.construct Core.kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, .field i]) →
      Bytes.RepAddressRef Core.addrTy h' b blk →
      ∃ (cb' : Ixon.Constant) (xs : Array Ixon.MutConst) (ind' : Ixon.Inductive),
        Ix.Cert.recordAt c.E (Core.ixAddr b) = some cb' ∧ cb'.info = .muts xs ∧
        xs[ZMod.val i]? = some (.indc ind') := by
  intro addr ptr h h' cs a b nl ty np ni nc u blk i ev hn good ha hld hb
  have hx := get_ci_induct_addr ev good.2 ha hld hb
  rcases hI.newKey hn with ⟨k, ind, hk, hxT⟩ | ⟨k, ind, j, hk, hj, hxC⟩
  · have hbh := L1.hashedBlockAt_of_get_ci_induct (c := appCtx c new) good ev ha hld hb
    obtain ⟨hbB, hik⟩ := iprj_key_member (i := ZMod.val i) hI.wf hI.decoded hI.held
      (hI.formerRec k ind hk) hbh (by rw [← hx, hxT])
    obtain ⟨ind', hmem⟩ := hI.member_le hk (le_of_toUInt64_eq (val_lt_uint64 i) hik)
    refine ⟨cb, ms, ind', ?_, hI.muts, hmem⟩
    rw [hbB]
    exact recordAt_of_recordOf hI.decoded hI.block
  · exfalso
    have hrec : recordOf c.E (Core.ixAddr a) = some (constructorProjection B k j) := by
      rw [hxC]
      exact hI.ctorRec k ind hk j hj
    obtain ⟨b', i', -, -, -, hinfo⟩ := get_ci_induct_record hI.decoded good.1 good.2 ev ha hld hrec
    simp [constructorProjection] at hinfo

/-- **`NewLoads.ctorIndRes`.** A new constructor at a hashed block's constructor key is a
constructor of a member of the installed block, whose former is stored at the member key. -/
theorem PointInstall.newCtorIndRes (hI : PointInstall c new B cb ms) :
    ∀ (b : _root_.Address) (i j : Nat) (cv : ConstantVal .anon) (nP nF : Nat),
      Core.HashedBlockAt c.E b →
      (appCtx c new).env.find? ((appCtx c new).stored.κ (Core.cprjAddr b i j)) =
        some (.ctorInfo cv nP nF) →
      ConstantInfo.ctorInfo cv nP nF ∈ new →
      (appCtx c new).stored.κ (Core.iprjAddr b i) ≠ Core.unresolvedKey := by
  intro b i j cv nP nF hbh hf hm
  obtain ⟨k, ind, j', hk, hj', hkey⟩ := hI.newCtor hf hm
  obtain ⟨hbB, hik, -⟩ :=
    cprj_key_member hI.wf hI.decoded hI.held (hI.ctorRec k ind hk j' hj') hbh hkey
  rw [hbB, iprjAddr_congr (b := B) hik]
  obtain ⟨ty₀, ty', -, -, -, -, hfT⟩ := hI.former k ind hk
  rw [appCtx_key_of_find hfT]
  exact Core.Resolved.ne

/-- **`NewLoads.projCtorTele`**, vacuous: the install stores no projection table
(`PointInstall.noTable`), and a constructor it stores is of a member whose former's key is fresh
in the prefix, so the prefix stores no table at that key's projection-table name either: every
key the prefix stores has its root stored (`haux`), and the table name's root is the former's
key. The two hypotheses are facts of the fold at the prefix: `AuxRootSynced` is kept by every
install (`Decl.Point.PointBlock.auxRootSynced`), and the formers' keys are fresh in the prefix
(`Decl.Point.PointBlock.freshF`). -/
theorem PointInstall.newProjCtorTele (hI : PointInstall c new B cb ms)
    (haux : Decl.AuxRootSynced c.env)
    (hfresh : ∀ (k : Nat) (ind : Ixon.Inductive), ms[k]? = some (.indc ind) →
      c.env.find? (Core.keyOf c.t (Core.iprjAddr B k)) = none) :
    ∀ (bp ip ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (b : Bytes.Address) (i : F),
      ObsFn Core.W "KernelModeled::proj_ctor" [bp, ip] h ptr h' cs →
      Core.Good (appCtx c new) cs → Bytes.RepAddressRef Core.addrTy h b bp → ip = .field i →
      ∀ (j : Nat) (cvC : ConstantVal .anon) (nP nF : Nat) (tbl : Ix.Kernel.ProjTable .anon),
        (appCtx c new).env.find? ((appCtx c new).stored.κ
          (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) j)) = some (.ctorInfo cvC nP nF) →
        (appCtx c new).env.find? (Ix.Kernel.projTableName
          ((appCtx c new).stored.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)))) =
          some (.projInfo tbl) →
        (ConstantInfo.ctorInfo cvC nP nF ∈ new ∨ ConstantInfo.projInfo tbl ∈ new) →
        Ix.Kernel.Expr.ctorTeleOk cvC.type (nP + nF) = true := by
  intro bp ip ptr h h' cs b i ev good hb hip j cvC nP nF tbl hctor htbl hm
  exfalso
  rcases hm with hm | hm
  · subst hip
    have hbh := L1.hashedBlockAt_of_proj_ctor (c := appCtx c new) good ev hb rfl
    obtain ⟨k, ind, j', hk, hj', hkey⟩ := hI.newCtor hctor hm
    obtain ⟨hbB, hik, -⟩ :=
      cprj_key_member hI.wf hI.decoded hI.held (hI.ctorRec k ind hk j' hj') hbh hkey
    obtain ⟨ty₀, ty', -, -, -, -, hfT⟩ := hI.former k ind hk
    have hκ : (appCtx c new).stored.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)) =
        Core.keyOf c.t (Core.iprjAddr B k) := by
      rw [hbB, iprjAddr_congr (b := B) hik]
      exact appCtx_key_of_find hfT
    rw [hκ] at htbl
    rcases find?_append_cases (env := c.env) new htbl with hm' | ho
    · exact hI.noTable tbl hm'
    · have hnone : c.env.find? (Ix.Kernel.projTableName (Core.keyOf c.t (Core.iprjAddr B k))) =
          none := haux.fresh_projTable (Decl.isBaseKey_keyOf c.t _) (hfresh k ind hk)
      rw [hnone] at ho
      cases ho
  · exact hI.noTable tbl hm

end

end IxVM.Refinement.Typing
