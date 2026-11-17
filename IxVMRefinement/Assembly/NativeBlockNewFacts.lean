import IxVMRefinement.Assembly.NativeBlockLoads
import IxVMRefinement.Assembly.NativeBlockOutsNamed

/-! # The new family's load facts after a native block's install: loads and records

`NewLoads` (`NativeBlockLoads.lean`) asks, at the environment after the install, for each field of
the load contract whose load or stored constant is new. This file gives the fields that read the
store and the new constants' values:

* `BlockInstall`: what the install and the block's record give about the new constants — the
  former at its key with the canonical annotation of its reading, each constructor at its key
  with the canonical annotation of its reading and the record's counts, and every new constant is
  at one of those keys or is a projection table;
* `get_ci_induct_addr`: **a load that returns an inductive is at the projection address of the
  member it names** — the circuit's `get_ci` hashes the record's bytes to the address and decodes
  them exactly, with valid (empty) tables, and a projection record with empty tables is the
  canonical serialization of its info. So no second record with the same projection info can be
  loaded at another address; no store fact is needed beyond the bound on the calls;
* `cprj_key_block`: the constructor twin of `iprj_key_block`;
* `BlockInstall.famNew`: a family witnessed by a new constant at a hashed block is the new block's
  member `0`;
* the fields `getCI`, `getIprj`, `getCprj`, `inductRecord`, `inductBlock`, `ctorIndRes`,
  `unitLike`, `unitLikeRaw` of `NewLoads` (`BlockInstall.newGetCI`, …).
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

/-! ## Two address facts -/

/-- **A load that returns an inductive is at the projection address of the member it names**:
the record the circuit loaded hashes to the address and decodes exactly with valid tables, and a
projection record with empty tables is the canonical serialization of its info, at the member's
projection address. -/
theorem get_ci_induct_addr {addr ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {a b : Bytes.Address} {nl ty np ni nc u blk : SourceValue F} {i : F}
    (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs) (hbound : Bounded cs)
    (ha : Bytes.RepAddressRef Core.addrTy h a addr)
    (hld : loadValue h' ptr =
      .ok (.construct Core.kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, .field i]))
    (hb : Bytes.RepAddressRef Core.addrTy h' b blk) :
    Core.ixAddr a = Core.iprjAddr (Core.ixAddr b) (ZMod.val i) := by
  obtain ⟨rawBytes, blkBytes, cm, cb, xs, ind, b', i', -, haddr, hde, -, -, -, -, -, hb', hidx, -,
    hinfo, -, -, htv⟩ := L1.inductRecord_raw_tables_of_get_ci ev hbound ha hld
  have hbb : b' = b := IxVMRep.repAddressRef_det U32.Goldilocks.compatible hb' hb
  rw [hbb] at hinfo
  have hii : i = i' := by
    injection hidx
  rw [← hii] at hinfo
  have hcan := (LoadedReads.iprj_canonical ind hde htv hinfo).2
  rw [LoadedReads.memberAddr_indc] at hcan
  rw [← haddr, hcan]
  show Core.iprjAddr (Core.ixAddr b) ((ZMod.val i).toUInt64.toNat) = _
  have hu : (((ZMod.val i).toUInt64.toNat).toUInt64 : UInt64) = (ZMod.val i).toUInt64 :=
    UInt64.ofNat_toNat
  unfold Core.iprjAddr
  rw [hu]

/-- **A constructor key of a hashed block that is the key of one of the new block's constructors
is that constructor's**: the twin of `iprj_key_block` (the store holds the constructor's
projection at its address; the projections a hashed block's addresses hold are its own). -/
theorem cprj_key_block {t : Ix.Kernel.RoleTable} (htwf : t.wf = true) {E : Ixon.Env}
    (hdec : L1.EnvDecoded E) (hP : HashedBlockProjectionsHeld E) {B b : _root_.Address}
    {j' : Nat} (hproj : recordOf E (ctorAddr B 0 j') = some (constructorProjection B 0 j'))
    (hbh : Core.HashedBlockAt E b) {i j : Nat}
    (hkey : Core.keyOf t (Core.cprjAddr b i j) = Core.keyOf t (Core.cprjAddr B 0 j')) :
    b = B ∧ i.toUInt64 = (0 : Nat).toUInt64 ∧ j.toUInt64 = j'.toUInt64 := by
  have hx : Core.cprjAddr b i j = Core.cprjAddr B 0 j' := Core.keyOf_inj htwf hkey
  have hrec : Ix.Cert.recordAt E (Core.cprjAddr b i j) = some (constructorProjection B 0 j') := by
    rw [hx, ← LoadedReads.ctorAddr_eq_cprjAddr]
    exact recordAt_of_recordOf hdec hproj
  have hinfo := (hP b hbh).2 i j _ hrec
  have h0 : (constructorProjection B 0 j').info = .cPrj ⟨(0 : Nat).toUInt64, j'.toUInt64, B⟩ := rfl
  rw [h0] at hinfo
  injection hinfo with hp
  injection hp with hidx hcidx hblk
  exact ⟨hblk.symm, hidx.symm, hcidx.symm⟩

/-- The member projection address reads its index as a 64-bit number. -/
theorem iprjAddr_of_toUInt64 {b : _root_.Address} {i : Nat}
    (hi : i.toUInt64 = (0 : Nat).toUInt64) : Core.iprjAddr b i = Core.iprjAddr b 0 := by
  unfold Core.iprjAddr
  rw [hi]

theorem toUInt64_zero_of_lt {i : Nat} (hi : i < UInt64.size)
    (h : i.toUInt64 = (0 : Nat).toUInt64) : i = 0 := by
  have e := congrArg UInt64.toNat h
  change (UInt64.ofNat i).toNat = (UInt64.ofNat 0).toNat at e
  rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt hi] at e
  simpa using e

theorem toUInt64_inj_of_lt {i j : Nat} (hi : i < UInt64.size) (hj : j < UInt64.size)
    (h : i.toUInt64 = j.toUInt64) : i = j := by
  have e := congrArg UInt64.toNat h
  change (UInt64.ofNat i).toNat = (UInt64.ofNat j).toNat at e
  rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at e
  exact e

/-! ## The install's new constants -/

/-- **The new constants of a native block's install, as the store reads them.** `c` is the
prefix context and `new` the constants the install puts in front. The store `c.E` (decoded,
holding at a hashed block's projection addresses that block's projections) holds the block `cb`
of one inductive member `ind` at `B`, the member's and the constructors' projection records; the
former is stored at its key with the canonical annotation of its reading and the capability
record `caps`; each constructor at its key with the canonical annotation of its reading and the
record's counts; every new constant is at one of those keys or is a projection table, and is the
constant the longer environment finds at its name. -/
structure BlockInstall (c : Core.Ctx) (new : List (ConstantInfo .anon)) (B : _root_.Address)
    (cb : Ixon.Constant) (ind : Ixon.Inductive) (caps : IndCaps .anon) : Prop where
  check : c.t.check = .ok ()
  decoded : L1.EnvDecoded c.E
  held : HashedBlockProjectionsHeld c.E
  block : recordOf c.E B = some cb
  muts : cb.info = .muts #[.indc ind]
  formerRec : recordOf c.E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind))
  ctorRec : ∀ j < ind.ctors.size,
    recordOf c.E (ctorAddr B 0 j) = some (constructorProjection B 0 j)
  bounds : ind.params.toNat < 2 ^ 56 ∧ ind.indices.toNat < 2 ^ 56 ∧ ind.ctors.size < 2 ^ 56
  used : Decl.UsedRefsStored c.t (appCtx c new).env cb
  former : ∃ ty₀ ty' : Ix.Kernel.Expr .anon,
    (exprReader c.t (fun x => c.E.blobs.get? x) cb id
      (blockSelf c.t B #[.indc ind])).read ind.typ = .ok ty₀ ∧
    ty₀.looseBVarsBounded 0 = true ∧
    ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧
    LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
      ((L1.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList 0 : Nat) : F) ind.typ ty₀ =
      some ty' ∧
    (appCtx c new).env.find? (Core.keyOf c.t (Core.iprjAddr B 0)) =
      some (.indInfo ⟨Core.keyOf c.t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ caps)
  ctor : ∀ j < ind.ctors.size, ∃ (ct : Ixon.Constructor) (cty cty' : Ix.Kernel.Expr .anon),
    ind.ctors[j]? = some ct ∧ ct.cidx.toNat = j ∧
    (exprReader c.t (fun x => c.E.blobs.get? x) cb id
      (blockSelf c.t B #[.indc ind])).read ct.typ = .ok cty ∧
    cty.looseBVarsBounded 0 = true ∧
    cty.allLevelParamsDefined (List.range ct.lvls.toNat) = true ∧
    LoadedReads.canonAnn cb (List.range ct.lvls.toNat)
      (((L1.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList 0 : Nat) : F) + 1 +
        ((j : Nat) : F)) ct.typ cty = some cty' ∧
    (appCtx c new).env.find? (Core.keyOf c.t (Core.cprjAddr B 0 j)) =
      some (.ctorInfo ⟨Core.keyOf c.t (Core.cprjAddr B 0 j), List.range ct.lvls.toNat, cty'⟩
        ct.params.toNat ct.fields.toNat)
  newName : ∀ ci ∈ new, ci.name = Core.keyOf c.t (Core.iprjAddr B 0) ∨
    (∃ j < ind.ctors.size, ci.name = Core.keyOf c.t (Core.cprjAddr B 0 j)) ∨
    ∃ tbl, ci = .projInfo tbl
  newFind : ∀ ci ∈ new, (appCtx c new).env.find? ci.name = some ci
  unit : ind.indices.toNat = 0 → ind.ctors.size = 1 →
    (∀ ct, ind.ctors[0]? = some ct → ct.fields.toNat = 0) →
    caps.unitlike = true ∧ caps.unitParams = ind.params.toNat
  free : Ix.Kernel.reservedBasisNames.contains (Core.keyOf c.t (Core.iprjAddr B 0)) = false

section
variable {c : Core.Ctx} {new : List (ConstantInfo .anon)} {B : _root_.Address}
  {cb : Ixon.Constant} {ind : Ixon.Inductive} {caps : IndCaps .anon}

theorem BlockInstall.wf (hI : BlockInstall c new B cb ind caps) : c.t.wf = true := by
  unfold Ix.Kernel.RoleTable.wf
  rw [hI.check]
  rfl

/-- A key the longer environment stores at an address is the table's. -/
theorem appCtx_key_of_find {x : _root_.Address} {ci : ConstantInfo .anon}
    (hf : (appCtx c new).env.find? (Core.keyOf c.t x) = some ci) :
    (appCtx c new).stored.κ x = Core.keyOf c.t x :=
  Core.Ctx.stored_key_of_find (c := appCtx c new) hf

/-- A new constant found at a key the longer context resolves for an address. -/
theorem appCtx_key_of_new {x : _root_.Address} {ci : ConstantInfo .anon}
    (hf : (appCtx c new).env.find? ((appCtx c new).stored.κ x) = some ci)
    (hres : ci.name ≠ Core.unresolvedKey) :
    (appCtx c new).stored.κ x = Core.keyOf c.t x := by
  have hn : ci.name = (appCtx c new).stored.κ x := Core.WhnfAux.name_of_find hf
  exact (appCtx c new).stored.key_eq (by rw [← hn]; exact hres)

/-- **The new inductive is the former**: an inductive the longer environment finds among the new
constants at an address's key is the stored former, at the former's key. -/
theorem BlockInstall.newInd (hI : BlockInstall c new B cb ind caps) {x : _root_.Address}
    {cv : ConstantVal .anon} {caps' : IndCaps .anon}
    (hf : (appCtx c new).env.find? ((appCtx c new).stored.κ x) = some (.indInfo cv caps'))
    (hm : ConstantInfo.indInfo cv caps' ∈ new) :
    Core.keyOf c.t x = Core.keyOf c.t (Core.iprjAddr B 0) ∧
      ∃ ty', cv = ⟨Core.keyOf c.t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ ∧
        caps' = caps := by
  have hn : cv.name = (appCtx c new).stored.κ x := Core.WhnfAux.name_of_find hf
  obtain ⟨ty₀, ty', -, -, -, -, hfT⟩ := hI.former
  rcases hI.newName _ hm with hT | ⟨j, hj, hC⟩ | ⟨tbl, htbl⟩
  · have hT' : cv.name = Core.keyOf c.t (Core.iprjAddr B 0) := hT
    have hκ : (appCtx c new).stored.κ x = Core.keyOf c.t (Core.iprjAddr B 0) := hn.symm.trans hT'
    have hκ' := (appCtx c new).stored.key_eq (a := x) (by rw [hκ]; exact Core.Resolved.ne)
    refine ⟨hκ'.symm.trans hκ, ?_⟩
    rw [hκ, hfT] at hf
    injection hf with hf
    injection hf with h1 h2
    exact ⟨ty', h1.symm, h2.symm⟩
  · exfalso
    obtain ⟨ct, cty, cty', -, -, -, -, -, -, hfC⟩ := hI.ctor j hj
    have hC' : cv.name = Core.keyOf c.t (Core.cprjAddr B 0 j) := hC
    rw [← hn, hC', hfC] at hf
    cases hf
  · cases htbl

/-- **The new constructor is the block's**: a constructor the longer environment finds among the
new constants at an address's key is at the key of one of the block's constructors. -/
theorem BlockInstall.newCtor (hI : BlockInstall c new B cb ind caps) {x : _root_.Address}
    {cv : ConstantVal .anon} {nP nF : Nat}
    (hf : (appCtx c new).env.find? ((appCtx c new).stored.κ x) = some (.ctorInfo cv nP nF))
    (hm : ConstantInfo.ctorInfo cv nP nF ∈ new) :
    ∃ j < ind.ctors.size, Core.keyOf c.t x = Core.keyOf c.t (Core.cprjAddr B 0 j) := by
  have hn : cv.name = (appCtx c new).stored.κ x := Core.WhnfAux.name_of_find hf
  rcases hI.newName _ hm with hT | ⟨j, hj, hC⟩ | ⟨tbl, htbl⟩
  · exfalso
    obtain ⟨ty₀, ty', -, -, -, -, hfT⟩ := hI.former
    have hT' : cv.name = Core.keyOf c.t (Core.iprjAddr B 0) := hT
    rw [← hn, hT', hfT] at hf
    cases hf
  · have hC' : cv.name = Core.keyOf c.t (Core.cprjAddr B 0 j) := hC
    have hκ : (appCtx c new).stored.κ x = Core.keyOf c.t (Core.cprjAddr B 0 j) := hn.symm.trans hC'
    have hκ' := (appCtx c new).stored.key_eq (a := x) (by rw [hκ]; exact Core.Resolved.ne)
    exact ⟨j, hj, hκ'.symm.trans hκ⟩
  · cases htbl

/-- **A family witnessed by a new constant at a hashed block is the new block's member `0`.** -/
theorem BlockInstall.famNew (hI : BlockInstall c new B cb ind caps) {b : _root_.Address}
    (hbh : Core.HashedBlockAt c.E b) {i : Nat} (hi : i < UInt64.size)
    (hfam : FamNew (appCtx c new).stored new b i) : b = B ∧ i = 0 := by
  rcases hfam with ⟨cv, caps', hf, hm⟩ | ⟨j, cv, nP, nF, hf, hm⟩
  · obtain ⟨hk, -⟩ := hI.newInd hf hm
    exact iprj_key_block hI.wf hI.decoded hI.held hI.formerRec hbh hi hk
  · obtain ⟨j', hj', hk⟩ := hI.newCtor hf hm
    obtain ⟨hb, hi0, -⟩ := cprj_key_block hI.wf hI.decoded hI.held (hI.ctorRec j' hj') hbh hk
    exact ⟨hb, toUInt64_zero_of_lt hi hi0⟩

/-- The block's members are stored at the longer environment. -/
theorem BlockInstall.blockStored (hI : BlockInstall c new B cb ind caps) :
    LoadedReads.BlockStored c.t (appCtx c new).env B #[.indc ind] := by
  apply LoadedReads.blockStored_of_members
  intro k m hm
  have hk : k = 0 := by
    have hlt : k < 1 := (Array.getElem?_eq_some_iff.mp hm).1
    omega
  subst hk
  have hmm : m = .indc ind := by simpa using hm.symm
  subst hmm
  obtain ⟨ty₀, ty', -, -, -, -, hfT⟩ := hI.former
  exact ⟨_, by rw [LoadedReads.memberAddr_indc]; exact hfT⟩


/-- The new keys at addresses are the former's and the constructors'. -/
theorem BlockInstall.newKey (hI : BlockInstall c new B cb ind caps) {x : _root_.Address}
    (hn : ∃ cn ∈ new, cn.name = Core.keyOf c.t x) :
    x = Core.iprjAddr B 0 ∨ ∃ j < ind.ctors.size, x = Core.cprjAddr B 0 j := by
  obtain ⟨cn, hcn, hname⟩ := hn
  rcases hI.newName cn hcn with hT | ⟨j, hj, hC⟩ | ⟨tbl, rfl⟩
  · exact Or.inl (Core.keyOf_inj hI.wf (hname.symm.trans hT))
  · exact Or.inr ⟨j, hj, Core.keyOf_inj hI.wf (hname.symm.trans hC)⟩
  · exact absurd hname.symm (Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf c.t x))

theorem BlockInstall.ctor_lt (hI : BlockInstall c new B cb ind caps) {j : Nat}
    (hj : j < ind.ctors.size) : j < UInt64.size :=
  Nat.lt_trans (Nat.lt_trans hj hI.bounds.2.2) (by decide)

theorem toNat_toUInt64_of_lt {n : Nat} (hn : n < UInt64.size) : n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

end

/-! ## The loads of the former and of the constructors -/

/-- **A load of the former's projection record**: its value is the record's inductive with the
record's counts, member index `0`. -/
theorem former_get_ci_value {E : Ixon.Env} {addr ptr : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} {a : Bytes.Address}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbound : Bounded cs)
    (ha : Bytes.RepAddressRef Core.addrTy h a addr)
    (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs) {B : _root_.Address}
    {cb : Ixon.Constant} {ind : Ixon.Inductive}
    (hrecA : recordOf E (Core.ixAddr a) = some (memberProjection B 0 (.indc ind)))
    (hblock : recordOf E B = some cb) (hmuts : cb.info = .muts #[.indc ind]) :
    ∃ tyPtr blkPtr : SourceValue F,
      loadValue h' ptr = .ok (.construct Core.kciEnum "Induct"
        [.field (ind.lvls.toNat : F), tyPtr, .field (ind.params.toNat : F),
          .field (ind.indices.toNat : F), .field (ind.ctors.size : F), L1.repBoolField ind.isUnsafe,
          blkPtr, .field ((0 : Nat) : F)]) ∧
      ind.params.toNat < 72057594037927936 ∧ ind.indices.toNat < 72057594037927936 ∧
      ind.ctors.size < 72057594037927936 := by
  obtain ⟨rawBytes, c', hh, haddr, hex, htv, hres⟩ := L1.get_ci_block_trace_spec hbound ha ev
  obtain ⟨lc, hget, hdecA⟩ := LoadedReads.recordOf_inv hrecA
  have hb : rawBytes = lc.rawBytes := Core.load_escape hget hnc rawBytes hh haddr
  have hc : c' = memberProjection B 0 (.indc ind) := by
    rw [hb, hdecA] at hex
    exact (Except.ok.inj hex).symm
  subst hc
  unfold L1.GetCIBlockTraceResult at hres
  have hinfo : (memberProjection B 0 (.indc ind)).info = .iPrj ⟨(0 : Nat).toUInt64, B⟩ := rfl
  rw [hinfo] at hres
  obtain ⟨hidx, blkBytes, cb', ms', ind', blobs, tree, plan, v₀, hhB, haB, hexB, hcb, hms,
    hhp, built, planned, hld₀, hraw, hlev⟩ := hres
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hblock
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hnc blkBytes hhB haB
  have hcB : cb' = cb := by
    rw [hbB, hdecB] at hexB
    exact (Except.ok.inj hexB).symm
  subst hcB
  have hmsEq : ms' = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hcb.symm.trans hmuts)
  subst hmsEq
  have h0 : ((0 : Nat).toUInt64).toNat = 0 := toNat_toUInt64_of_lt (by decide)
  have h0' : (⟨(0 : Nat).toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat = 0 := h0
  rw [h0'] at hms hraw
  have hiEq : ind' = ind := by
    have e : (Ixon.MutConst.indc ind : Ixon.MutConst) = .indc ind' := Option.some.inj hms
    exact (Ixon.MutConst.indc.inj e).symm
  subst hiEq
  obtain ⟨hlvls, hp56, hi56, hc56, hidx56, tyPtr, blkPtr, b, hb_eq, hb_rep, hv, rty⟩ := hraw
  subst hv
  exact ⟨tyPtr, blkPtr, hld₀, hp56, hi56, hc56⟩

/-- **The record a loaded inductive's address holds is the loaded one**, with the block the
load named. -/
theorem get_ci_induct_record {E : Ixon.Env} {addr ptr : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} {a : Bytes.Address} {nl ty np ni nc u blk idx : SourceValue F}
    (hdec : L1.EnvDecoded E) (hnc : ¬ View.HashedCollision { env := E } [] cs)
    (hbound : Bounded cs) (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs)
    (ha : Bytes.RepAddressRef Core.addrTy h a addr)
    (hld : loadValue h' ptr =
      .ok (.construct Core.kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]))
    {c₀ : Ixon.Constant} (hrec : recordOf E (Core.ixAddr a) = some c₀) :
    ∃ (b : Bytes.Address) (i : F), Ix.Cert.recordAt E (Core.ixAddr a) = some c₀ ∧
      Bytes.RepAddressRef Core.addrTy h' b blk ∧ idx = .field i ∧
      c₀.info = .iPrj ⟨(ZMod.val i).toUInt64, Core.ixAddr b⟩ := by
  obtain ⟨rawBytes, blkBytes, cm, cb', xs, ind', b, i, hh, haddr, hde, -, -, -, -, -, hb, hidx,
    -, hinfo, -, -⟩ := L1.inductRecord_raw_of_get_ci ev hbound ha hld
  obtain ⟨lc, hget, hdec₀⟩ := LoadedReads.recordOf_inv hrec
  have hbytes : rawBytes = lc.rawBytes := Core.load_escape hget hnc rawBytes hh haddr
  have hcm : cm = c₀ := by
    rw [hbytes, hdec₀] at hde
    exact (Except.ok.inj hde).symm
  subst hcm
  exact ⟨b, i, recordAt_of_recordOf hdec hrec, hb, hidx, hinfo⟩

section
variable {c : Core.Ctx} {new : List (ConstantInfo .anon)} {B : _root_.Address}
  {cb : Ixon.Constant} {ind : Ixon.Inductive} {caps : IndCaps .anon}

/-- **`NewLoads.getCI`.** -/
theorem BlockInstall.newGetCI (hI : BlockInstall c new B cb ind caps) :
    ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address),
      ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs → Core.Good (appCtx c new) cs →
      Bytes.RepAddressRef Core.addrTy h a addr →
      (∃ cn ∈ new, cn.name = Core.keyOf c.t (Core.ixAddr a)) →
        ∃ ci, (appCtx c new).env.find? ((appCtx c new).stored.κ (Core.ixAddr a)) = some ci ∧
          Core.CIPtrRep (appCtx c new).stored.κ h' ptr ci := by
  intro addr ptr h h' cs a ev good ha hn
  have h0 : ((0 : Nat).toUInt64).toNat = 0 := toNat_toUInt64_of_lt (by decide)
  rcases hI.newKey hn with hx | ⟨j, hj, hx⟩
  · obtain ⟨ty₀, ty', hty, hlbb, hdef, hcan, hfT⟩ := hI.former
    have hrecA : recordOf c.E (Core.ixAddr a) = some (memberProjection B 0 (.indc ind)) := by
      rw [hx]
      exact hI.formerRec
    obtain ⟨-, ty'', hcan', -, -, hrep⟩ := LoadedReads.get_ci_iprj_canon
      (p := ⟨(0 : Nat).toUInt64, B⟩) hI.check good.1 good.2 ha ev hrecA rfl hI.block hI.muts
      (by
        show (#[.indc ind] : Array Ixon.MutConst)[((0 : Nat).toUInt64).toNat]? = some (.indc ind)
        rw [h0]
        rfl)
      hty hlbb hdef
    have hcan'' : LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
        ((L1.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList
          ((0 : Nat).toUInt64).toNat : Nat) : F) ind.typ ty₀ = some ty'' := hcan'
    rw [h0] at hcan''
    have e : ty'' = ty' := Option.some.inj (hcan''.symm.trans hcan)
    subst e
    have hfA : (appCtx c new).env.find? (Core.keyOf c.t (Core.ixAddr a)) =
        some (.indInfo ⟨Core.keyOf c.t (Core.ixAddr a), List.range ind.lvls.toNat, ty''⟩ caps) := by
      rw [hx]
      exact hfT
    refine ⟨_, ?_, hrep (appCtx c new).env c.lim hI.used hI.blockStored caps⟩
    rw [appCtx_key_of_find hfA]
    exact hfA
  · obtain ⟨ct, cty, cty', hct, hcidx, hty, hlbb, hdef, hcan, hfC⟩ := hI.ctor j hj
    have hjj : j.toUInt64.toNat = j := toNat_toUInt64_of_lt (hI.ctor_lt hj)
    have hrecA : recordOf c.E (Core.ixAddr a) = some (constructorProjection B 0 j) := by
      rw [hx, ← LoadedReads.ctorAddr_eq_cprjAddr]
      exact hI.ctorRec j hj
    obtain ⟨-, ty'', hcan', -, -, hrep⟩ := LoadedReads.get_ci_cprj_canon
      (p := ⟨(0 : Nat).toUInt64, j.toUInt64, B⟩) (ct := ct) hI.check good.1 good.2 ha ev hrecA rfl
      hI.block hI.muts
      (by
        show (#[.indc ind] : Array Ixon.MutConst)[((0 : Nat).toUInt64).toNat]? = some (.indc ind)
        rw [h0]
        rfl)
      (by
        show ind.ctors[j.toUInt64.toNat]? = some ct
        rw [hjj]
        exact hct)
      (by
        show ct.cidx.toNat = j.toUInt64.toNat
        rw [hjj]
        exact hcidx)
      hty hlbb hdef
    have hcan'' : LoadedReads.canonAnn cb (List.range ct.lvls.toNat)
        (((L1.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList
          ((0 : Nat).toUInt64).toNat : Nat) : F) + 1 + ((j.toUInt64.toNat : Nat) : F))
        ct.typ cty = some ty'' := hcan'
    rw [h0, hjj] at hcan''
    have e : ty'' = cty' := Option.some.inj (hcan''.symm.trans hcan)
    subst e
    have hfA : (appCtx c new).env.find? (Core.keyOf c.t (Core.ixAddr a)) =
        some (.ctorInfo ⟨Core.keyOf c.t (Core.ixAddr a), List.range ct.lvls.toNat, ty''⟩
          ct.params.toNat ct.fields.toNat) := by
      rw [hx]
      exact hfC
    refine ⟨_, ?_, hrep (appCtx c new).env c.lim hI.used hI.blockStored ⟨_, hfA⟩⟩
    rw [appCtx_key_of_find hfA]
    exact hfA

/-- **`NewLoads.getIprj`.** -/
theorem BlockInstall.newGetIprj (hI : BlockInstall c new B cb ind caps) :
    ∀ (bp ptr : SourceValue F) (i : F) (h h' : Heap F) (cs : List (Call F)) (b : Bytes.Address),
      ObsFn Core.W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' cs →
      FamNew (appCtx c new).stored new (Core.ixAddr b) (ZMod.val i) →
      Core.Good (appCtx c new) cs → Bytes.RepAddressRef Core.addrTy h b bp →
        ∃ ci, (appCtx c new).env.find?
            ((appCtx c new).stored.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i))) = some ci ∧
          Core.CIPtrRep (appCtx c new).stored.κ h' ptr ci := by
  intro bp ptr i h h' cs b ev hfam good hb
  have hbh := L1.hashedBlockAt_of_get_ci_iprj (c := appCtx c new) good hb ev
  obtain ⟨hbB, hi0⟩ := hI.famNew hbh (val_lt_uint64 i) hfam
  obtain ⟨ty₀, ty', hty, hlbb, hdef, hcan, hfT⟩ := hI.former
  have hblock' : recordOf c.E (Core.ixAddr b) = some cb := by
    rw [hbB]
    exact hI.block
  have hmem : (#[.indc ind] : Array Ixon.MutConst)[ZMod.val i]? = some (.indc ind) := by
    rw [hi0]
    rfl
  have hty' : (exprReader c.t (fun x => c.E.blobs.get? x) cb id
      (blockSelf c.t (Core.ixAddr b) #[.indc ind])).read ind.typ = .ok ty₀ := by
    rw [hbB]
    exact hty
  obtain ⟨ty'', hcan', -, -, hrep⟩ := LoadedReads.get_ci_iprj_load_canon hI.check good.1 good.2
    hb ev hblock' hI.muts hmem hty' hlbb hdef
  have hcan'' : LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
      ((L1.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList (ZMod.val i) : Nat) : F)
      ind.typ ty₀ = some ty'' := hcan'
  rw [hi0] at hcan''
  have e : ty'' = ty' := Option.some.inj (hcan''.symm.trans hcan)
  subst e
  have hbs : LoadedReads.BlockStored c.t (appCtx c new).env (Core.ixAddr b) #[.indc ind] := by
    rw [hbB]
    exact hI.blockStored
  have hfA : (appCtx c new).env.find? (Core.keyOf c.t (Core.iprjAddr (Core.ixAddr b) (ZMod.val i))) =
      some (.indInfo ⟨Core.keyOf c.t (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)),
        List.range ind.lvls.toNat, ty''⟩ caps) := by
    rw [hbB, hi0]
    exact hfT
  refine ⟨_, ?_, hrep (appCtx c new).env c.lim hI.used hbs caps⟩
  rw [appCtx_key_of_find hfA]
  exact hfA

/-- **`NewLoads.getCprj`.** -/
theorem BlockInstall.newGetCprj (hI : BlockInstall c new B cb ind caps) :
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
  obtain ⟨hbB, hi0⟩ := hI.famNew hbh (val_lt_uint64 i) hfam
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
  have hmsEq : (#[.indc ind] : Array Ixon.MutConst) = ms' :=
    Ixon.ConstantInfo.muts.inj (hI.muts.symm.trans hcb)
  subst hmsEq
  have hiEq : ind = ind' := by
    have hms0 : (#[.indc ind] : Array Ixon.MutConst).toList[ZMod.val i]? = some (.indc ind') := hms
    rw [hi0] at hms0
    exact Ixon.MutConst.indc.inj (Option.some.inj hms0)
  subst hiEq
  have hct : ind.ctors[ZMod.val j]? = some ct' := by
    rw [← Array.getElem?_toList]
    exact hcts
  have hjs : ZMod.val j < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hct).1
  obtain ⟨ct, cty, cty', hct₀, hcidx, hty, hlbb, hdef, hcan, hfC⟩ := hI.ctor (ZMod.val j) hjs
  have hmem : (#[.indc ind] : Array Ixon.MutConst)[ZMod.val i]? = some (.indc ind) := by
    rw [hi0]
    rfl
  have hty' : (exprReader c.t (fun x => c.E.blobs.get? x) cb id
      (blockSelf c.t (Core.ixAddr b) #[.indc ind])).read ct.typ = .ok cty := by
    rw [hbB]
    exact hty
  obtain ⟨ty'', hcan', -, -, hrep⟩ := LoadedReads.get_ci_cprj_load_canon hI.check good.1 good.2
    hb ev hblock' hI.muts hmem hct₀ hcidx hty' hlbb hdef
  have hcan'' : LoadedReads.canonAnn cb (List.range ct.lvls.toNat)
      (((L1.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList (ZMod.val i) : Nat) : F) +
        1 + ((ZMod.val j : Nat) : F)) ct.typ cty = some ty'' := hcan'
  rw [hi0] at hcan''
  have e : ty'' = cty' := Option.some.inj (hcan''.symm.trans hcan)
  subst e
  have hfA : (appCtx c new).env.find?
      (Core.keyOf c.t (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) (ZMod.val j))) =
      some (.ctorInfo ⟨Core.keyOf c.t (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) (ZMod.val j)),
        List.range ct.lvls.toNat, ty''⟩ ct.params.toNat ct.fields.toNat) := by
    rw [hbB, hi0]
    exact hfC
  have hbs : LoadedReads.BlockStored c.t (appCtx c new).env (Core.ixAddr b) #[.indc ind] := by
    rw [hbB]
    exact hI.blockStored
  have hr := hrep (appCtx c new).env c.lim hI.used hbs ⟨_, hfA⟩
  refine ⟨⟨_, hr⟩, fun cv nP nF hf => ?_⟩
  rw [appCtx_key_of_find hfA, hfA] at hf
  rw [← Option.some.inj hf]
  exact hr

/-- **`NewLoads.inductRecord`.** -/
theorem BlockInstall.newInductRecord (hI : BlockInstall c new B cb ind caps) :
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
    rcases hI.newKey hn with hx | ⟨j, hj, hx⟩
    · exact ⟨_, by rw [hx]; exact hI.formerRec⟩
    · exact ⟨_, by rw [hx, ← LoadedReads.ctorAddr_eq_cprjAddr]; exact hI.ctorRec j hj⟩
  obtain ⟨b, i, hrecA, hb, hidx, hinfo⟩ :=
    get_ci_induct_record hI.decoded good.1 good.2 ev ha hld hrec
  exact ⟨c₀, b, i, hrecA, hb, hidx, hinfo⟩

/-- **`NewLoads.inductBlock`.** -/
theorem BlockInstall.newInductBlock (hI : BlockInstall c new B cb ind caps) :
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
  rcases hI.newKey hn with hxT | ⟨j, hj, hxC⟩
  · have hbh := L1.hashedBlockAt_of_get_ci_induct (c := appCtx c new) good ev ha hld hb
    obtain ⟨hbB, hi0⟩ := iprj_key_block hI.wf hI.decoded hI.held hI.formerRec hbh
      (val_lt_uint64 i) (by rw [← hx, hxT])
    refine ⟨cb, #[.indc ind], ind, ?_, hI.muts, ?_⟩
    · rw [hbB]
      exact recordAt_of_recordOf hI.decoded hI.block
    · rw [hi0]
      rfl
  · exfalso
    have hrec : recordOf c.E (Core.ixAddr a) = some (constructorProjection B 0 j) := by
      rw [hxC, ← LoadedReads.ctorAddr_eq_cprjAddr]
      exact hI.ctorRec j hj
    obtain ⟨b', i', -, -, -, hinfo⟩ := get_ci_induct_record hI.decoded good.1 good.2 ev ha hld hrec
    simp [constructorProjection] at hinfo

/-- **`NewLoads.ctorIndRes`.** -/
theorem BlockInstall.newCtorIndRes (hI : BlockInstall c new B cb ind caps) :
    ∀ (b : _root_.Address) (i j : Nat) (cv : ConstantVal .anon) (nP nF : Nat),
      Core.HashedBlockAt c.E b →
      (appCtx c new).env.find? ((appCtx c new).stored.κ (Core.cprjAddr b i j)) =
        some (.ctorInfo cv nP nF) →
      ConstantInfo.ctorInfo cv nP nF ∈ new →
      (appCtx c new).stored.κ (Core.iprjAddr b i) ≠ Core.unresolvedKey := by
  intro b i j cv nP nF hbh hf hm
  obtain ⟨j', hj', hk⟩ := hI.newCtor hf hm
  obtain ⟨hbB, hi0, -⟩ := cprj_key_block hI.wf hI.decoded hI.held (hI.ctorRec j' hj') hbh hk
  rw [hbB, iprjAddr_of_toUInt64 hi0]
  obtain ⟨ty₀, ty', -, -, -, -, hfT⟩ := hI.former
  rw [appCtx_key_of_find hfT]
  exact Core.Resolved.ne


/-- The record's counts read off the field elements of a load (each below `2 ^ 56`). -/
theorem field_count_eq {n : Nat} {x : F} (hn : n < 72057594037927936)
    (h : (Value.field (n : F) : SourceValue F) = .field x) : ZMod.val x = n := by
  injection h with e
  rw [← e]
  exact ZMod.val_natCast_of_lt (Nat.lt_trans hn (by decide))

/-- **The loaded inductive is the new former, with the record's counts**, where its member is the
new block's member `0`. -/
theorem BlockInstall.formerLoad (hI : BlockInstall c new B cb ind caps)
    {ap ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {a : Bytes.Address}
    {nl ty u blk : SourceValue F} {p m i : F}
    (ev : ObsFn Core.W "Ingress::get_ci" [ap] h ptr h' cs) (good : Core.Good (appCtx c new) cs)
    (ha : Bytes.RepAddressRef Core.addrTy h a ap)
    (hld : loadValue h' ptr = .ok (.construct Core.kciEnum "Induct"
      [nl, ty, .field p, .field m, .field 1, u, blk, .field i]))
    (hxa : Core.ixAddr a = Core.iprjAddr B 0) :
    ZMod.val p = ind.params.toNat ∧ ZMod.val m = ind.indices.toNat ∧ ind.ctors.size = 1 := by
  obtain ⟨tyPtr, blkPtr, hld₀, hp56, hi56, hc56⟩ := former_get_ci_value good.1 good.2 ha ev
    (by rw [hxa]; exact hI.formerRec) hI.block hI.muts
  rw [hld₀] at hld
  have hv := Except.ok.inj hld
  simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hv
  obtain ⟨-, -, hp, hm, hn, -⟩ := hv
  refine ⟨field_count_eq hp56 hp, field_count_eq hi56 hm, ?_⟩
  have e := field_count_eq hc56 hn
  rw [ZMod.val_one] at e
  exact e.symm

/-- **`NewLoads.unitLike`.** -/
theorem BlockInstall.newUnitLike (hI : BlockInstall c new B cb ind caps) :
    ∀ (ap ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address)
      (nl ty u blk : SourceValue F) (p i : F) (b : Bytes.Address)
      (cvT : ConstantVal .anon) (caps' : IndCaps .anon) (cvC : ConstantVal .anon) (nPc : Nat),
      ObsFn Core.W "Ingress::get_ci" [ap] h ptr h' cs → Core.Good (appCtx c new) cs →
      Bytes.RepAddressRef Core.addrTy h a ap →
      loadValue h' ptr = .ok (.construct Core.kciEnum "Induct"
        [nl, ty, .field p, .field 0, .field 1, u, blk, .field i]) →
      Bytes.RepAddressRef Core.addrTy h' b blk →
      (appCtx c new).env.find? ((appCtx c new).stored.κ (Core.ixAddr a)) =
        some (.indInfo cvT caps') →
      Core.FewInductives (appCtx c new) (Core.ixAddr b) →
      (appCtx c new).env.find? ((appCtx c new).stored.κ
        (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) 0)) = some (.ctorInfo cvC nPc 0) →
      (ConstantInfo.indInfo cvT caps' ∈ new ∨ ConstantInfo.ctorInfo cvC nPc 0 ∈ new) →
      caps'.unitlike = true ∧ caps'.unitParams = ZMod.val p ∧
        (Ix.Kernel.reservedBasisNames.contains ((appCtx c new).stored.κ (Core.ixAddr a)) = false ∨
          (ZMod.val p = 0 ∧ ∀ us, Ix.Kernel.isUnitLikeTy (appCtx c new).env
            (.const ((appCtx c new).stored.κ (Core.ixAddr a)) us) = true)) := by
  intro ap ptr h h' cs a nl ty u blk p i b cvT caps' cvC nPc ev good ha hld hb hfT hfew hfC hm
  have hx := get_ci_induct_addr ev good.2 ha hld hb
  have hbh := L1.hashedBlockAt_of_get_ci_induct (c := appCtx c new) good ev ha hld hb
  have hBi : Core.ixAddr b = B ∧ ZMod.val i = 0 := by
    rcases hm with hm | hm
    · obtain ⟨hk, -⟩ := hI.newInd hfT hm
      exact iprj_key_block hI.wf hI.decoded hI.held hI.formerRec hbh (val_lt_uint64 i)
        (by rw [← hx]; exact hk)
    · obtain ⟨j', hj', hk⟩ := hI.newCtor hfC hm
      obtain ⟨hbB, hi0, -⟩ := cprj_key_block hI.wf hI.decoded hI.held (hI.ctorRec j' hj') hbh hk
      exact ⟨hbB, toUInt64_zero_of_lt (val_lt_uint64 i) hi0⟩
  obtain ⟨hbB, hi0⟩ := hBi
  have hxa : Core.ixAddr a = Core.iprjAddr B 0 := by rw [hx, hbB, hi0]
  obtain ⟨ty₀, ty', -, -, -, -, hfT₀⟩ := hI.former
  have hfA : (appCtx c new).env.find? (Core.keyOf c.t (Core.ixAddr a)) =
      some (.indInfo ⟨Core.keyOf c.t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ caps) := by
    rw [hxa]
    exact hfT₀
  have hκa := appCtx_key_of_find hfA
  rw [hκa, hfA] at hfT
  injection hfT with hfT
  injection hfT with hcv hcaps
  subst hcaps
  obtain ⟨hpv, hiv, hsz⟩ := hI.formerLoad ev good ha hld hxa
  have hi0' : ind.indices.toNat = 0 := by rw [← hiv, ZMod.val_zero]
  -- constructor `0` has no field
  obtain ⟨ct, cty, cty', hct, -, -, -, -, -, hfC₀⟩ := hI.ctor 0 (by omega)
  rw [hbB, hi0, appCtx_key_of_find hfC₀, hfC₀] at hfC
  injection hfC with hfC
  injection hfC with hcvC hnpC hnf
  obtain ⟨hu1, hu2⟩ := hI.unit hi0' hsz (fun ct' h' => by
    rw [hct] at h'
    rw [← Option.some.inj h']
    exact hnf)
  refine ⟨hu1, hu2.trans hpv.symm, Or.inl ?_⟩
  rw [hκa, hxa]
  exact hI.free

/-- **`NewLoads.unitLikeRaw`.** -/
theorem BlockInstall.newUnitLikeRaw (hI : BlockInstall c new B cb ind caps) :
    ∀ (ap ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address)
      (nl ty u blk : SourceValue F) (p i : F) (b : Bytes.Address)
      (cvT : ConstantVal .anon) (caps' : IndCaps .anon),
      ObsFn Core.W "Ingress::get_ci" [ap] h ptr h' cs → Core.Good (appCtx c new) cs →
      Bytes.RepAddressRef Core.addrTy h a ap →
      loadValue h' ptr = .ok (.construct Core.kciEnum "Induct"
        [nl, ty, .field p, .field 0, .field 1, u, blk, .field i]) →
      Bytes.RepAddressRef Core.addrTy h' b blk →
      (appCtx c new).env.find? ((appCtx c new).stored.κ (Core.ixAddr a)) =
        some (.indInfo cvT caps') →
      ConstantInfo.indInfo cvT caps' ∈ new → Core.FewInductives (appCtx c new) (Core.ixAddr b) →
      Core.ZeroFieldCtorLoad (appCtx c new).stored b i → Core.NonrecursiveLoad (appCtx c new).stored a →
      caps'.unitlike = true ∧ caps'.unitParams = ZMod.val p ∧
        (Ix.Kernel.reservedBasisNames.contains ((appCtx c new).stored.κ (Core.ixAddr a)) = false ∨
          (ZMod.val p = 0 ∧ ∀ us, Ix.Kernel.isUnitLikeTy (appCtx c new).env
            (.const ((appCtx c new).stored.κ (Core.ixAddr a)) us) = true)) := by
  intro ap ptr h h' cs a nl ty u blk p i b cvT caps' ev good ha hld hb hfT hm hfew hz hn
  have hx := get_ci_induct_addr ev good.2 ha hld hb
  have hbh := L1.hashedBlockAt_of_get_ci_induct (c := appCtx c new) good ev ha hld hb
  obtain ⟨hk, ty', hcv, hcaps⟩ := hI.newInd hfT hm
  subst hcaps
  have hxa : Core.ixAddr a = Core.iprjAddr B 0 := Core.keyOf_inj hI.wf hk
  obtain ⟨hbB, hi0⟩ := iprj_key_block hI.wf hI.decoded hI.held hI.formerRec hbh (val_lt_uint64 i)
    (by rw [← hx]; exact hk)
  obtain ⟨hpv, hiv, hsz⟩ := hI.formerLoad ev good ha hld hxa
  have hi0' : ind.indices.toNat = 0 := by rw [← hiv, ZMod.val_zero]
  -- constructor `0` has no field: the load of the zero-field observation is the record's
  obtain ⟨ct, cty, cty', hct, hcidx, hty, hlbb, hdef, -, -⟩ := hI.ctor 0 (by omega)
  have hblock' : recordOf c.E (Core.ixAddr b) = some cb := by
    rw [hbB]
    exact hI.block
  have hmem : (#[.indc ind] : Array Ixon.MutConst)[ZMod.val i]? = some (.indc ind) := by
    rw [hi0]
    rfl
  have hty' : (exprReader c.t (fun x => c.E.blobs.get? x) cb id
      (blockSelf c.t (Core.ixAddr b) #[.indc ind])).read ct.typ = .ok cty := by
    rw [hbB]
    exact hty
  obtain ⟨tyPtr, blkPtr, bz, tyA, RA, hld₀, -, -, -, -, hf56, -⟩ := LoadedReads.ctor_load_canon hI.check
    hz.good.1 hz.good.2 hz.blockRep hz.observed hblock' hI.muts hmem
    (by rw [ZMod.val_zero]; exact hct) (by rw [ZMod.val_zero]; exact hcidx) hty' hlbb hdef
  obtain ⟨nl', ty'', blk', idx', cidx', np', u', hz0⟩ := hz.zeroFields
  rw [hld₀] at hz0
  have hv := Except.ok.inj hz0
  simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hv
  obtain ⟨-, -, -, -, -, -, hnf, -⟩ := hv
  have hnf' : ct.fields.toNat = 0 := by
    have e := field_count_eq hf56 hnf
    rw [ZMod.val_zero] at e
    exact e.symm
  obtain ⟨hu1, hu2⟩ := hI.unit hi0' hsz (fun ct' h' => by
    rw [hct] at h'
    rw [← Option.some.inj h']
    exact hnf')
  obtain ⟨ty₀, ty'', -, -, -, -, hfT₀⟩ := hI.former
  have hfA : (appCtx c new).env.find? (Core.keyOf c.t (Core.ixAddr a)) =
      some (.indInfo ⟨Core.keyOf c.t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty''⟩ caps') := by
    rw [hxa]
    exact hfT₀
  refine ⟨hu1, hu2.trans hpv.symm, Or.inl ?_⟩
  rw [appCtx_key_of_find hfA, hxa]
  exact hI.free

end

end IxVM.Refinement.Typing
