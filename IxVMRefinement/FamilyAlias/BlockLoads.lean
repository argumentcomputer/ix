import IxVMRefinement.FamilyAlias.BlockRow
import IxVMRefinement.Assembly.NativeBlockNewFacts
import IxVMRefinement.L1.HashedBlock

/-! # The load facts at the family step's new constants that do not read the family check

`NewLoads` (`Assembly/NativeBlockLoads.lean`) asks, at the environment after the family step,
each field of the load contract whose load or stored constant is new. The step stores the
block's inductives and constructors and the family record's recursors at the keys of their
constant addresses, and the aliases (definitions) at derived keys. Ten fields hold from the
records at those addresses, the store, the route fact at the block and the walk's check of the
block, with no fact of the family check (`FamLoadCtx.newLoads`):

* `projFire`: the step stores no projection table;
* `inductRecord`, `inductBlock`, `ctorIndRes`: a load of a new inductive reads the member's
  projection record and its block; a new constructor's member is a new inductive;
* `projTables`, `projTablesAt`, `projCtorTele`, `eta`: each is handed an observation that the
  block of a new inductive or constructor is on the native route (`block_is_modeled` answering
  `0`, directly or inside `proj_ctor`); that block is the family's (a hashed block holds its own
  projection records), which is modeled at the store: the hypotheses are refuted;
* `unitLike`, `unitLikeRaw`: their conclusions ask the unit-like bit, unset at the step; their
  hypotheses are refuted. The loaded inductive is a member of the family's block
  (`FamLoadCtx.member_of_load`), a block of at most one inductive (`FewInductives`), whose member
  has no index and one constructor with no field (the load's counts and, for `unitLike`, the
  stored constructor's field count, `FamLoadCtx.ctorCounts`; for `unitLikeRaw`, the zero-field
  load). A modeled block of one inductive has no such constructor (`FamLoadCtx.unitFree`: the
  dispatch's scan answers `0` at it, `FamilyAlias/UnitFree.lean`).

The other four are `FamilyLoadsCheck`: the loads of the new constants (`getCI`, `getIprj`,
`getCprj`: the circuit loads a member's canonical annotated form, which the family check's
stored types have to be) and `etaIota`, whose conclusion asks the η bit the step stores as
unset. -/

universe u

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)

set_option linter.unusedVariables false

/-! ## The fields that read the family check -/

section Check
open IxVM.Refinement.Core

/-- **The load facts at the family step's new constants that read the family check**: the four
fields of `NewLoads` the store, the records and the route fact do not give (module
docstring). -/
structure FamilyLoadsCheck (c : ScopedCtx) (new : List (ConstantInfo .anon)) : Prop where
  getCI : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Good c.toCtx cs →
    Bytes.RepAddressRef addrTy h a addr → (∃ cn ∈ new, cn.name = keyOf c.t (ixAddr a)) →
      ∃ ci, c.env.find? (c.κ (ixAddr a)) = some ci ∧ CIPtrRep c.κ h' ptr ci
  getCprj : ∀ (bp ptr : SourceValue F) (i j : F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address),
    ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field j] h ptr h' cs →
      FamNew c new (ixAddr b) (ZMod.val i) → Good c.toCtx cs →
    Bytes.RepAddressRef addrTy h b bp →
      (∃ ci₀, CIPtrRep c.κ h' ptr ci₀) ∧
      ∀ cv nP nF, c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) (ZMod.val j))) =
          some (.ctorInfo cv nP nF) → CIPtrRep c.κ h' ptr (.ctorInfo cv nP nF)
  getIprj : ∀ (bp ptr : SourceValue F) (i : F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address),
    ObsFn W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' cs →
      FamNew c new (ixAddr b) (ZMod.val i) → Good c.toCtx cs →
    Bytes.RepAddressRef addrTy h b bp →
      ∃ ci, c.env.find? (c.κ (iprjAddr (ixAddr b) (ZMod.val i))) = some ci ∧ CIPtrRep c.κ h' ptr ci
  etaIota : ∀ (pp ptr nl ty u blk : SourceValue F) (h1 h2 : Heap F) (cs1 : List (Call F))
      (pa b : Bytes.Address) (i m : F) (cvT cvc : Ix.Kernel.ConstantVal .anon)
      (caps : Ix.Kernel.IndCaps .anon) (cnP cnF : Nat) (us : List KLevel) (l : KLevel),
    ObsFn W "Ingress::get_ci" [pp] h1 ptr h2 cs1 → Good c.toCtx cs1 →
    Bytes.RepAddressRef addrTy h1 pa pp →
    loadValue h2 ptr = .ok (.construct kciEnum "Induct"
      [nl, ty, .field m, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h2 b blk →
    c.env.find? (c.κ (ixAddr pa)) = some (.indInfo cvT caps) →
    c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) = some (.ctorInfo cvc cnP cnF) →
    (∃ (bq : SourceValue F) (h3 h4 : Heap F) (cs3 : List (Call F)),
      ObsFn W "KernelModeled::block_is_multi" [bq] h3 (.field 0) h4 cs3 ∧ Good c.toCtx cs3 ∧
        Bytes.RepAddressRef addrTy h3 b bq) →
    (∃ (sp v : SourceValue F) (h5 h6 : Heap F) (cs5 : List (Call F)),
      ObsFn W "KernelWhnf::struct_is_rec" [sp] h5 v h6 cs5 ∧ v ≠ .field 1 ∧ Good c.toCtx cs5 ∧
        Bytes.RepAddressRef addrTy h5 pa sp) →
    piSortAt (ZMod.val m) (posOf cvT.levelParams cvT.type) = some l →
    (Ix.Kernel.Level.subst (List.range us.length) us l).isNeverZero = true →
    (ConstantInfo.indInfo cvT caps ∈ new ∨ ConstantInfo.ctorInfo cvc cnP cnF ∈ new) →
    (caps.eta = true ∧
      caps.etaCtor = some (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) ∧ caps.etaFields = cnF ∧
      caps.etaParams = cnP ∧ cnP = ZMod.val m ∧ cvc.levelParams = cvT.levelParams) ∧
      EtaUseFacts c.env (c.κ (ixAddr pa))
      (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) cvT caps cnP cnF


end Check

/-! ## What the step's store and records give -/

section
open IxVM.Consistency

/-- **What the family step gives the load facts**, at the prefix context `C` and the new constants
`new`: a well-formed table, a decoded store that holds a hashed block's projection records, the
block `cb` (members `ms`) at `A` and the family record `crb` (members `rs`) at `rb` with their
projection records, the route fact at `A`, every new constant at the key of a constant address of
the two records or a definition at a derived key, and every such address stored; at a block of
one inductive, the first constructor stored with the record's counts, and a field in it where
the member has no index and one constructor. -/
structure FamLoadCtx (C : Core.Ctx) (new : List (ConstantInfo .anon)) (A : _root_.Address)
    (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (rb : _root_.Address) (crb : Ixon.Constant)
    (rs : Array Ixon.MutConst) : Prop where
  wf : C.t.wf = true
  decoded : L1.EnvDecoded C.E
  held : HashedBlockProjectionsHeld C.E
  muts : cb.info = .muts ms
  indcs : ∀ m ∈ ms.toList, ∃ ind, m = .indc ind
  rmuts : crb.info = .muts rs
  recrs : ∀ m ∈ rs.toList, ∃ r, m = .recr r
  members : ∀ i m, ms[i]? = some m → recordOf C.E (memberAddr A i m) = some (memberProjection A i m)
  ctors : ∀ i ind j, ms[i]? = some (.indc ind) → j < ind.ctors.size →
    recordOf C.E (ctorAddr A i j) = some (constructorProjection A i j)
  rmembers : ∀ i m, rs[i]? = some m →
    recordOf C.E (memberAddr rb i m) = some (memberProjection rb i m)
  record : recordOf C.E A = some cb
  route : ModeledAt C.E A
  newName : ∀ cn ∈ new, (∃ x, FamAddr A cb rb crb x ∧ cn.name = Core.keyOf C.t x) ∨
    ((∃ cv v hint, cn = .defnInfo cv v hint) ∧ ∃ n d, cn.name = Ix.Kernel.auxKey n d)
  found : ∀ x, FamAddr A cb rb crb x →
    ∃ ci, (appCtx C new).env.find? (Core.keyOf C.t x) = some ci
  /-- A block of one inductive with no index and one constructor, modeled at the store: that
  constructor has a field. -/
  unitFree : ∀ ind, ms = #[.indc ind] → ind.indices.toNat = 0 → ind.ctors.size = 1 →
    ∀ ct, ind.ctors[0]? = some ct → ct.fields.toNat ≠ 0
  /-- The constant stored at the key of the first constructor of a block of one inductive has
  the record's parameter and field counts. -/
  ctorCounts : ∀ ind ct, ms = #[.indc ind] → ind.ctors[0]? = some ct → ∀ ci,
    (appCtx C new).env.find? (Core.keyOf C.t (Core.cprjAddr A 0 0)) = some ci →
    ∃ cv, ci = .ctorInfo cv ct.params.toNat ct.fields.toNat

variable {C : Core.Ctx} {new : List (ConstantInfo .anon)} {A rb : _root_.Address}
  {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}

/-- **The record at a constant address of the two records**, by kind: an inductive member's or a
constructor's projection of the block, or a recursor projection. -/
theorem FamLoadCtx.recordOf_at (hL : FamLoadCtx C new A cb ms rb crb rs) {x : _root_.Address}
    (hx : FamAddr A cb rb crb x) :
    ∃ cm, recordOf C.E x = some cm ∧
      ((∃ i ind, ms[i]? = some (.indc ind) ∧ x = Core.iprjAddr A i ∧
          cm.info = .iPrj ⟨i.toUInt64, A⟩) ∨
        (∃ i ind j, ms[i]? = some (.indc ind) ∧ j < ind.ctors.size ∧ x = Core.cprjAddr A i j ∧
          cm.info = .cPrj ⟨i.toUInt64, j.toUInt64, A⟩) ∨
        (∃ p, cm.info = .rPrj p)) := by
  rcases hx with ⟨⟨-, hs⟩ | ⟨ms', i, m, hinfo', hget, hxm | ⟨ind, j, hind, hj, hxc⟩⟩⟩ |
      ⟨⟨-, hs⟩ | ⟨rs', i, m, hinfo', hget, hxm | ⟨ind, j, hind, hj, hxc⟩⟩⟩
  · exact (standalone_not_block hs ⟨ms, hL.muts⟩).elim
  · have e : ms' = ms := Ixon.ConstantInfo.muts.inj (hinfo'.symm.trans hL.muts)
    rw [e] at hget
    obtain ⟨ind, rfl⟩ := hL.indcs m (by simpa using Array.mem_of_getElem? hget)
    have hrec : recordOf C.E x = some (memberProjection A i (.indc ind)) := by
      rw [hxm]
      exact hL.members i _ hget
    exact ⟨_, hrec, Or.inl ⟨i, ind, hget, hxm, rfl⟩⟩
  · have e : ms' = ms := Ixon.ConstantInfo.muts.inj (hinfo'.symm.trans hL.muts)
    rw [e] at hget
    rw [hind] at hget
    have hrec : recordOf C.E x = some (constructorProjection A i j) := by
      rw [hxc]
      exact hL.ctors i ind j hget hj
    exact ⟨_, hrec, Or.inr (Or.inl ⟨i, ind, j, hget, hj, hxc, rfl⟩)⟩
  · exact (standalone_not_block hs ⟨rs, hL.rmuts⟩).elim
  · have e : rs' = rs := Ixon.ConstantInfo.muts.inj (hinfo'.symm.trans hL.rmuts)
    rw [e] at hget
    obtain ⟨r, rfl⟩ := hL.recrs m (by simpa using Array.mem_of_getElem? hget)
    have hrec : recordOf C.E x = some (memberProjection rb i (.recr r)) := by
      rw [hxm]
      exact hL.rmembers i _ hget
    exact ⟨_, hrec, Or.inr (Or.inr ⟨_, rfl⟩)⟩
  · have e : rs' = rs := Ixon.ConstantInfo.muts.inj (hinfo'.symm.trans hL.rmuts)
    rw [e] at hget
    obtain ⟨r, hr⟩ := hL.recrs m (by simpa using Array.mem_of_getElem? hget)
    rw [hind] at hr
    exact nomatch hr

/-- **A hashed block whose member projection address is a family address is the family's
block.** -/
theorem FamLoadCtx.iprj_block (hL : FamLoadCtx C new A cb ms rb crb rs) {b : _root_.Address}
    (hbh : Core.HashedBlockAt C.E b) {i : Nat} {x : _root_.Address} (hx : FamAddr A cb rb crb x)
    (hy : Core.iprjAddr b i = x) : b = A := by
  obtain ⟨cm, hrec, hk⟩ := hL.recordOf_at hx
  have hrec' : Ix.Cert.recordAt C.E (Core.iprjAddr b i) = some cm := by
    rw [hy]
    exact recordAt_of_recordOf hL.decoded hrec
  have hinfo := (hL.held b hbh).1 i cm hrec'
  rcases hk with ⟨i', ind, -, -, h'⟩ | ⟨i', ind, j', -, -, -, h'⟩ | ⟨p, h'⟩
  · rw [h'] at hinfo
    exact (congrArg Ixon.InductiveProj.block (Ixon.ConstantInfo.iPrj.inj hinfo)).symm
  · rw [h'] at hinfo
    exact nomatch hinfo
  · rw [h'] at hinfo
    exact nomatch hinfo

/-- **A hashed block whose constructor projection address is a family address is the family's
block**, at an inductive member of it with the same index. -/
theorem FamLoadCtx.cprj_block (hL : FamLoadCtx C new A cb ms rb crb rs) {b : _root_.Address}
    (hbh : Core.HashedBlockAt C.E b) {i j : Nat} {x : _root_.Address}
    (hx : FamAddr A cb rb crb x) (hy : Core.cprjAddr b i j = x) :
    b = A ∧ ∃ (i' : Nat) (ind : Ixon.Inductive), ms[i']? = some (.indc ind) ∧
      i.toUInt64 = i'.toUInt64 := by
  obtain ⟨cm, hrec, hk⟩ := hL.recordOf_at hx
  have hrec' : Ix.Cert.recordAt C.E (Core.cprjAddr b i j) = some cm := by
    rw [hy]
    exact recordAt_of_recordOf hL.decoded hrec
  have hinfo := (hL.held b hbh).2 i j cm hrec'
  rcases hk with ⟨i', ind, -, -, h'⟩ | ⟨i', ind, j', hget, -, -, h'⟩ | ⟨p, h'⟩
  · rw [h'] at hinfo
    exact nomatch hinfo
  · rw [h'] at hinfo
    have hp := Ixon.ConstantInfo.cPrj.inj hinfo
    exact ⟨(congrArg Ixon.ConstructorProj.block hp).symm, i', ind, hget,
      (congrArg Ixon.ConstructorProj.idx hp).symm⟩
  · rw [h'] at hinfo
    exact nomatch hinfo

/-- The longer context's key at an address that is the key of a family address is the table's:
the two addresses are one. -/
theorem FamLoadCtx.kappa_eq (hL : FamLoadCtx C new A cb ms rb crb rs) {y x : _root_.Address}
    (hk : (appCtx C new).stored.κ y = Core.keyOf C.t x) : y = x := by
  have h1 : (appCtx C new).stored.κ y = Core.keyOf C.t y :=
    (appCtx C new).stored.key_eq (a := y) (by rw [hk]; exact Core.Resolved.ne)
  exact Core.keyOf_inj hL.wf (h1.symm.trans hk)

/-- **A new constant that is no definition is at the key of a family address.** -/
theorem FamLoadCtx.member_name (hL : FamLoadCtx C new A cb ms rb crb rs)
    {cn : ConstantInfo .anon} (hm : cn ∈ new) (hnd : ∀ cv v hint, cn ≠ .defnInfo cv v hint) :
    ∃ x, FamAddr A cb rb crb x ∧ cn.name = Core.keyOf C.t x := by
  rcases hL.newName cn hm with h | ⟨⟨cv, v, hint, he⟩, -⟩
  · exact h
  · exact (hnd cv v hint he).elim

/-- **The block of a family a new constant witnesses is the family's block**, where it is a
hashed block. -/
theorem FamLoadCtx.famNew_block (hL : FamLoadCtx C new A cb ms rb crb rs) {b : _root_.Address}
    (hbh : Core.HashedBlockAt C.E b) {i : Nat} (hfam : FamNew (appCtx C new).stored new b i) :
    b = A := by
  rcases hfam with ⟨cv, caps, hf, hm⟩ | ⟨j, cv, nP, nF, hf, hm⟩
  · obtain ⟨x, hx, hname⟩ := hL.member_name hm (fun _ _ _ h => nomatch h)
    have hn : cv.name = (appCtx C new).stored.κ (Core.iprjAddr b i) :=
      Core.WhnfAux.name_of_find hf
    exact hL.iprj_block hbh hx (hL.kappa_eq (hn.symm.trans hname))
  · obtain ⟨x, hx, hname⟩ := hL.member_name hm (fun _ _ _ h => nomatch h)
    have hn : cv.name = (appCtx C new).stored.κ (Core.cprjAddr b i j) :=
      Core.WhnfAux.name_of_find hf
    exact (hL.cprj_block hbh hx (hL.kappa_eq (hn.symm.trans hname))).1

/-- **A hashed block whose member projection address is a family address is the family's
block**, at an inductive member of it with the same index. -/
theorem FamLoadCtx.iprj_block_idx (hL : FamLoadCtx C new A cb ms rb crb rs) {b : _root_.Address}
    (hbh : Core.HashedBlockAt C.E b) {i : Nat} {x : _root_.Address} (hx : FamAddr A cb rb crb x)
    (hy : Core.iprjAddr b i = x) :
    b = A ∧ ∃ (i' : Nat) (ind : Ixon.Inductive), ms[i']? = some (.indc ind) ∧
      i.toUInt64 = i'.toUInt64 := by
  obtain ⟨cm, hrec, hk⟩ := hL.recordOf_at hx
  have hrec' : Ix.Cert.recordAt C.E (Core.iprjAddr b i) = some cm := by
    rw [hy]
    exact recordAt_of_recordOf hL.decoded hrec
  have hinfo := (hL.held b hbh).1 i cm hrec'
  rcases hk with ⟨i', ind, hget, -, h'⟩ | ⟨i', ind, j', -, -, -, h'⟩ | ⟨p, h'⟩
  · rw [h'] at hinfo
    have hp := Ixon.ConstantInfo.iPrj.inj hinfo
    exact ⟨(congrArg Ixon.InductiveProj.block hp).symm, i', ind, hget,
      (congrArg Ixon.InductiveProj.idx hp).symm⟩
  · rw [h'] at hinfo
    exact nomatch hinfo
  · rw [h'] at hinfo
    exact nomatch hinfo

/-- **A block of the family's of at most one inductive is a block of one inductive.** -/
theorem FamLoadCtx.one_of_few (hL : FamLoadCtx C new A cb ms rb crb rs)
    (hfew : Core.FewInductives (appCtx C new) A) {i' : Nat} {ind : Ixon.Inductive}
    (hget : ms[i']? = some (.indc ind)) : ms = #[.indc ind] := by
  have hle := hfew cb ms (recordAt_of_recordOf hL.decoded hL.record) hL.muts
  have hf : ms.toList.filter Core.isIndc = ms.toList := by
    apply List.filter_eq_self.mpr
    intro m hm
    obtain ⟨ind', rfl⟩ := hL.indcs m hm
    rfl
  rw [hf, Array.length_toList] at hle
  have hlt : i' < ms.size := (Array.getElem?_eq_some_iff.mp hget).1
  obtain ⟨m, hm⟩ := Claim.array_of_size_one ms (by omega)
  subst hm
  have hi : i' = 0 := by
    have h1 : i' < 1 := hlt
    omega
  subst hi
  have e : m = .indc ind := by simpa using hget
  rw [e]

/-- **An inductive loaded at a member of the family's block, where the block is of at most one
inductive**: the loaded inductive is the block's only member, at index `0`, where the load's
inductive or its first constructor is new. -/
theorem FamLoadCtx.member_of_load (hL : FamLoadCtx C new A cb ms rb crb rs)
    {ap ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {a b : Bytes.Address}
    {nl ty np ni nc u blk : SourceValue F} {i : F}
    (ev : ObsFn Core.W "Ingress::get_ci" [ap] h ptr h' cs) (good : Core.Good (appCtx C new) cs)
    (ha : Bytes.RepAddressRef Core.addrTy h a ap)
    (hld : loadValue h' ptr = .ok (.construct Core.kciEnum "Induct"
      [nl, ty, np, ni, nc, u, blk, .field i]))
    (hb : Bytes.RepAddressRef Core.addrTy h' b blk)
    (hnew : (∃ cvT caps, (appCtx C new).env.find? ((appCtx C new).stored.κ (Core.ixAddr a)) =
        some (.indInfo cvT caps) ∧ ConstantInfo.indInfo cvT caps ∈ new) ∨
      (∃ cvC nPc nF, (appCtx C new).env.find? ((appCtx C new).stored.κ
        (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) 0)) = some (.ctorInfo cvC nPc nF) ∧
        ConstantInfo.ctorInfo cvC nPc nF ∈ new))
    (hfew : Core.FewInductives (appCtx C new) (Core.ixAddr b)) :
    Core.ixAddr b = A ∧ ZMod.val i = 0 ∧
      ∃ ind, ms = #[.indc ind] ∧ Core.ixAddr a = Core.iprjAddr A 0 := by
  have hx := get_ci_induct_addr ev good.2 ha hld hb
  have hbh := L1.hashedBlockAt_of_get_ci_induct good ev ha hld hb
  obtain ⟨hbA, i', ind, hget, hidx⟩ : Core.ixAddr b = A ∧ ∃ (i' : Nat) (ind : Ixon.Inductive),
      ms[i']? = some (.indc ind) ∧ (ZMod.val i).toUInt64 = i'.toUInt64 := by
    rcases hnew with ⟨cvT, caps, hfT, hm⟩ | ⟨cvC, nPc, nF, hfC, hm⟩
    · obtain ⟨x, hx', hname⟩ := hL.member_name hm (fun _ _ _ h => nomatch h)
      have hn : cvT.name = (appCtx C new).stored.κ (Core.ixAddr a) :=
        Core.WhnfAux.name_of_find hfT
      have hax : Core.ixAddr a = x := hL.kappa_eq (hn.symm.trans hname)
      exact hL.iprj_block_idx hbh hx' (hx.symm.trans hax)
    · obtain ⟨x, hx', hname⟩ := hL.member_name hm (fun _ _ _ h => nomatch h)
      have hn : cvC.name =
          (appCtx C new).stored.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) 0) :=
        Core.WhnfAux.name_of_find hfC
      exact hL.cprj_block hbh hx' (hL.kappa_eq (hn.symm.trans hname))
  rw [hbA] at hfew
  have hms := hL.one_of_few hfew hget
  have hi0 : i' = 0 := by
    rw [hms] at hget
    have h1 : i' < 1 := (Array.getElem?_eq_some_iff.mp hget).1
    omega
  subst hi0
  have hval : ZMod.val i = 0 := toUInt64_zero_of_lt (val_lt_uint64 i) hidx
  exact ⟨hbA, hval, ind, hms, by rw [hx, hbA, hval]⟩

/-- **The counts of the only member of a block of one inductive, as a load of it reads them.** -/
theorem FamLoadCtx.member_counts (hL : FamLoadCtx C new A cb ms rb crb rs)
    {ind : Ixon.Inductive} (hms : ms = #[.indc ind])
    {ap ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {a : Bytes.Address}
    {nl ty u blk : SourceValue F} {p m n i : F}
    (ev : ObsFn Core.W "Ingress::get_ci" [ap] h ptr h' cs) (good : Core.Good (appCtx C new) cs)
    (ha : Bytes.RepAddressRef Core.addrTy h a ap)
    (hld : loadValue h' ptr = .ok (.construct Core.kciEnum "Induct"
      [nl, ty, .field p, .field m, .field n, u, blk, .field i]))
    (hxa : Core.ixAddr a = Core.iprjAddr A 0) :
    ZMod.val m = ind.indices.toNat ∧ ZMod.val n = ind.ctors.size := by
  subst hms
  obtain ⟨tyPtr, blkPtr, hld₀, -, hi56, hc56⟩ := former_get_ci_value (E := C.E) good.1 good.2 ha
    ev (by rw [hxa]; exact hL.members 0 (.indc ind) rfl) hL.record hL.muts
  rw [hld₀] at hld
  have hv := Except.ok.inj hld
  injection hv with _ _ hargs
  injection hargs with _ hargs
  injection hargs with _ hargs
  injection hargs with _ hargs
  injection hargs with hni hargs
  injection hargs with hnc _
  exact ⟨field_count_eq hi56 hni, field_count_eq hc56 hnc⟩

/-- **`proj_ctor` observes the native route at its block**: it asserts `block_is_modeled = 0`. -/
theorem nativeAt_of_proj_ctor {c : Core.Ctx} {cs : List (Call F)} (hg : Core.Good c cs)
    {b : Bytes.Address} {bp ip ptr : SourceValue F} {h h' : Heap F}
    (ev : ObsFn Core.W "KernelModeled::proj_ctor" [bp, ip] h ptr h' cs)
    (hb : Bytes.RepAddressRef Core.addrTy h b bp) : NativeAt c.E (Core.ixAddr b) := by
  obtain ⟨v1, m2, cs12, cs26, ev14, ev28, hc52⟩ := Obs.«KernelModeled::proj_ctor».obs ev
  obtain ⟨v12, m15, cs23, ev25, heq40, -, -, hc45⟩ :=
    Obs.«KernelModeled::assert_proj_allowed».obs ev14
  subst heq40
  have hg' : Core.Good c cs23 := hg.sub fun cl hcl => by simp [hc52, hc45, hcl]
  exact ⟨bp, h, m15, cs23, b, ev25, hg'.1, hg'.2, hb, rfl⟩

/-- **The load facts at the family step's new constants** from those that read the family check
(module docstring). -/
theorem FamLoadCtx.newLoads (hL : FamLoadCtx C new A cb ms rb crb rs)
    (hK : FamilyLoadsCheck (appCtx C new).stored new) :
    NewLoads (appCtx C new).stored new where
  getCI := hK.getCI
  getCprj := hK.getCprj
  getIprj := hK.getIprj
  inductRecord := by
    intro addr ptr h h' cs a nl ty np ni nc u blk idx ev hn good ha hld
    obtain ⟨cn, hcn, hname⟩ := hn
    rcases hL.newName cn hcn with ⟨x, hx, hx'⟩ | ⟨-, n, d, hnd⟩
    · have hax : Core.ixAddr a = x := Core.keyOf_inj hL.wf (hname.symm.trans hx')
      obtain ⟨cm, hrec, -⟩ := hL.recordOf_at hx
      rw [← hax] at hrec
      obtain ⟨b, i, hrecA, hb, hidx, hinfo⟩ :=
        get_ci_induct_record hL.decoded good.1 good.2 ev ha hld hrec
      exact ⟨cm, b, i, hrecA, hb, hidx, hinfo⟩
    · exact (keyOf_nonAux C.t (Core.ixAddr a) n d (hname.symm.trans hnd)).elim
  projTables := by
    intro bp ip ptr h h' cs b i ev good hb hip hfam hperm
    exfalso
    have hbh := L1.hashedBlockAt_of_proj_ctor good ev hb hip
    have hbA := hL.famNew_block hbh hfam
    have hnat := nativeAt_of_proj_ctor good ev hb
    rw [hbA] at hnat
    exact hL.route hnat
  projTablesAt := by
    intro bp sap ptr nl ty np u blk h h' h1 h2 cs cs1 b s i ev good hb ev1 good1 hs hld hb2
      j cvC nP nF hf hm hpos
    exfalso
    have hbh := L1.hashedBlockAt_of_get_ci_induct good1 ev1 hs hld hb2
    obtain ⟨x, hx, hname⟩ := hL.member_name hm (fun _ _ _ h => nomatch h)
    have hn : cvC.name =
        (appCtx C new).stored.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) j) :=
      Core.WhnfAux.name_of_find hf
    have hbA := (hL.cprj_block hbh hx (hL.kappa_eq (hn.symm.trans hname))).1
    have hnat : NativeAt C.E (Core.ixAddr b) := ⟨bp, h, h', cs, b, ev, good.1, good.2, hb, rfl⟩
    rw [hbA] at hnat
    exact hL.route hnat
  unitLike := by
    intro ap ptr h h' cs a nl ty u blk p i b cvT caps cvC nPc ev good ha hld hb hfT hfew hfC hm
    exfalso
    obtain ⟨hbA, hval, ind, hms, hxa⟩ := hL.member_of_load ev good ha hld hb
      (hm.imp (fun hm => ⟨cvT, caps, hfT, hm⟩) (fun hm => ⟨cvC, nPc, 0, hfC, hm⟩)) hfew
    obtain ⟨hidx, hsz⟩ := hL.member_counts hms ev good ha hld hxa
    rw [ZMod.val_zero] at hidx
    rw [ZMod.val_one] at hsz
    obtain ⟨ct, hct⟩ : ∃ ct, ind.ctors[0]? = some ct := by
      obtain ⟨x, hx⟩ := Claim.array_of_size_one ind.ctors hsz.symm
      exact ⟨x, by simp [hx]⟩
    have hx0 : FamAddr A cb rb crb (Core.cprjAddr A 0 0) :=
      Or.inl (Or.inr ⟨ms, 0, .indc ind, hL.muts, by subst hms; rfl,
        Or.inr ⟨ind, 0, rfl, by omega, rfl⟩⟩)
    obtain ⟨ci₀, hf₀⟩ := hL.found _ hx0
    have hκ := Core.Ctx.stored_key_of_find (c := appCtx C new) hf₀
    rw [hbA, hval, hκ] at hfC
    obtain ⟨cv, hcv⟩ := hL.ctorCounts ind ct hms hct _ hfC
    injection hcv with _ _ hnf
    exact hL.unitFree ind hms hidx.symm hsz.symm ct hct hnf.symm
  unitLikeRaw := by
    intro ap ptr h h' cs a nl ty u blk p i b cvT caps ev good ha hld hb hfT hm hfew hz hnr
    exfalso
    obtain ⟨hbA, hval, ind, hms, hxa⟩ := hL.member_of_load ev good ha hld hb
      (Or.inl ⟨cvT, caps, hfT, hm⟩) hfew
    obtain ⟨hidx, hsz⟩ := hL.member_counts hms ev good ha hld hxa
    rw [ZMod.val_zero] at hidx
    rw [ZMod.val_one] at hsz
    obtain ⟨ct, hct⟩ : ∃ ct, ind.ctors[0]? = some ct := by
      obtain ⟨x, hx⟩ := Claim.array_of_size_one ind.ctors hsz.symm
      exact ⟨x, by simp [hx]⟩
    -- the zero-field load reads constructor `0` of the block's record
    obtain ⟨-, -, -, blkBytes, cb', ms', ind', ct', blobs, v', hh, haddr, hexB, -, hcb', hms',
      hct', -, hldv, hraw⟩ := L1.get_ci_cprj_spec hz.good.2 hz.blockRep hz.observed
    obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hL.record
    have hbB : blkBytes = lcB.rawBytes :=
      Core.load_escape hgetB hz.good.1 blkBytes hh (haddr.trans hbA)
    have e1 : cb' = cb := by
      rw [hbB, hdecB] at hexB
      exact (Except.ok.inj hexB).symm
    subst cb'
    have e2 : ms' = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans (hms ▸ hL.muts))
    subst ms'
    rw [hval] at hms'
    have e3 : ind' = ind := by
      have e : (#[Ixon.MutConst.indc ind] : Array Ixon.MutConst).toList[0]? = some (.indc ind) :=
        rfl
      exact Ixon.MutConst.indc.inj (Option.some.inj (hms'.symm.trans e))
    subst ind'
    rw [ZMod.val_zero] at hct'
    have e4 : ct' = ct := by
      have e : ind.ctors.toList[0]? = some ct := by
        rw [Array.getElem?_toList]
        exact hct
      exact Option.some.inj (hct'.symm.trans e)
    subst ct'
    obtain ⟨nl', ty', blk', idx', cidx', np', u', hz0⟩ := hz.zeroFields
    rw [hldv] at hz0
    obtain ⟨-, -, -, hf56, -, tyPtrC, blkPtrC, bC, -, -, hvC, -⟩ := hraw
    rw [hvC] at hz0
    have hv := Except.ok.inj hz0
    injection hv with _ _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with _ hargs
    injection hargs with hnf _
    have hf0 : ct.fields.toNat = 0 := by
      have e := field_count_eq hf56 hnf
      rw [ZMod.val_zero] at e
      exact e.symm
    exact hL.unitFree ind hms hidx.symm hsz.symm ct hct hf0
  eta := by
    intro ac b sa i j cvc cvT caps cnP cnF us l bp ptr nl ty np u blk idx h1 h2 cs1 hfC hcn hpos
      ev good hb hld hfT hmod hsort hnz hrec hsa hnew
    exfalso
    have hbh := L1.hashedBlockAt_of_get_ci_iprj good hb ev
    have hbA : Core.ixAddr b = A := by
      rcases hnew with hm | hm
      · obtain ⟨x, hx, hname⟩ := hL.member_name hm (fun _ _ _ h => nomatch h)
        exact (hL.cprj_block hbh hx (hL.kappa_eq (hcn.symm.trans hname))).1
      · obtain ⟨x, hx, hname⟩ := hL.member_name hm (fun _ _ _ h => nomatch h)
        have hn : cvT.name =
            (appCtx C new).stored.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)) :=
          Core.WhnfAux.name_of_find hfT
        exact hL.iprj_block hbh hx (hL.kappa_eq (hn.symm.trans hname))
    obtain ⟨bq, h3, h4, cs3, ev3, good3, hb3⟩ := hmod
    have hnat : NativeAt C.E (Core.ixAddr b) :=
      ⟨bq, h3, h4, cs3, b, ev3, good3.1, good3.2, hb3, rfl⟩
    rw [hbA] at hnat
    exact hL.route hnat
  etaIota := hK.etaIota
  inductBlock := by
    intro addr ptr h h' cs a b nl ty np ni nc u blk i ev hn good ha hld hb
    obtain ⟨cn, hcn, hname⟩ := hn
    rcases hL.newName cn hcn with ⟨x, hx, hx'⟩ | ⟨-, n, d, hnd⟩
    · have hax : Core.ixAddr a = x := Core.keyOf_inj hL.wf (hname.symm.trans hx')
      have hia := get_ci_induct_addr ev good.2 ha hld hb
      have hbh := L1.hashedBlockAt_of_get_ci_induct good ev ha hld hb
      have hbA : Core.ixAddr b = A := hL.iprj_block hbh hx (hia.symm.trans hax)
      obtain ⟨rawBytes, blkBytes, cm, cb', xs, ind, b', i', -, -, -, -, hhb, hab, hdeb, -, hb',
        hidx, -, -, hcb', hxs⟩ := L1.inductRecord_raw_of_get_ci ev good.2 ha hld
      have hbb : b' = b := Bytes.repAddressRef_inj U32.Goldilocks.compatible hb' hb
      rw [hbb] at hab
      have hii : i' = i := by
        injection hidx with e
        exact e.symm
      rw [hii] at hxs
      obtain ⟨lc, hget, hdec₀⟩ := LoadedReads.recordOf_inv hL.record
      rw [← hbA] at hget
      have hbytes : blkBytes = lc.rawBytes := Core.load_escape hget good.1 blkBytes hhb hab
      rw [hbytes, hdec₀] at hdeb
      have e : cb' = cb := (Except.ok.inj hdeb).symm
      rw [e] at hcb'
      refine ⟨cb, xs, ind, ?_, hcb', hxs⟩
      rw [hbA]
      exact recordAt_of_recordOf hL.decoded hL.record
    · exact (keyOf_nonAux C.t (Core.ixAddr a) n d (hname.symm.trans hnd)).elim
  projCtorTele := by
    intro bp ip ptr h h' cs b i ev good hb hip j cvC nP nF tbl hfC hfT hm
    exfalso
    rcases hm with hm | hm
    · have hbh := L1.hashedBlockAt_of_proj_ctor good ev hb hip
      obtain ⟨x, hx, hname⟩ := hL.member_name hm (fun _ _ _ h => nomatch h)
      have hn : cvC.name =
          (appCtx C new).stored.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) j) :=
        Core.WhnfAux.name_of_find hfC
      have hbA := (hL.cprj_block hbh hx (hL.kappa_eq (hn.symm.trans hname))).1
      have hnat := nativeAt_of_proj_ctor good ev hb
      rw [hbA] at hnat
      exact hL.route hnat
    · rcases hL.newName _ hm with ⟨x, -, hname⟩ | ⟨⟨cv, v, hint, he⟩, -⟩
      · have hn : (ConstantInfo.projInfo tbl).name = Ix.Kernel.projTableName
            ((appCtx C new).stored.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i))) :=
          Core.WhnfAux.name_of_find hfT
        exact Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf C.t x)
          (hname.symm.trans hn)
      · cases he
  projFire := by
    intro k tbl hm hf hsort
    exfalso
    have hn : (ConstantInfo.projInfo tbl).name = Ix.Kernel.projTableName k :=
      Core.WhnfAux.name_of_find hf
    rcases hL.newName _ hm with ⟨x, -, hname⟩ | ⟨⟨cv, v, hint, he⟩, -⟩
    · exact Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf C.t x) (hname.symm.trans hn)
    · cases he
  ctorIndRes := by
    intro b i j cv nP nF hbh hf hm
    obtain ⟨x, hx, hname⟩ := hL.member_name hm (fun _ _ _ h => nomatch h)
    have hn : cv.name = (appCtx C new).stored.κ (Core.cprjAddr b i j) :=
      Core.WhnfAux.name_of_find hf
    obtain ⟨hbA, i', ind, hget, hidx⟩ := hL.cprj_block hbh hx (hL.kappa_eq (hn.symm.trans hname))
    have he : Core.iprjAddr b i = Core.iprjAddr A i' := by
      rw [hbA]
      unfold Core.iprjAddr
      rw [hidx]
    rw [he]
    have hx' : FamAddr A cb rb crb (Core.iprjAddr A i') :=
      Or.inl (Or.inr ⟨ms, i', .indc ind, hL.muts, hget, Or.inl rfl⟩)
    obtain ⟨ci, hfi⟩ := hL.found _ hx'
    rw [Core.Ctx.stored_key_of_find (c := appCtx C new) hfi]
    exact Core.Resolved.ne

end

end IxVM.Refinement.Typing.FamilyAlias
