import IxVMRefinement.FamilyAlias.BlockRow
import IxVMRefinement.FamilyAlias.StructRecScan
import IxVMRefinement.Assembly.NativeBlockNewFacts
import IxVMRefinement.L1.HashedBlock
import IxVMRefinement.TwinFamily.Reload

/-! # The load facts at the family step's new constants that do not read the family check

`NewLoads` (`Assembly/NativeBlockLoads.lean`) asks, at the environment after the family step,
each field of the load contract whose load or stored constant is new. The step stores the
block's inductives and constructors and the family record's recursors at the keys of their
constant addresses, and the aliases (definitions) at derived keys. Ten fields hold from the
records at those addresses, the store, the route fact at the block and the walk's check of the
block, with no fact of the family check (`FamLoadCtx.newLoads`); eleven fields in all:

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
  dispatch's scan answers `0` at it, `FamilyAlias/UnitFree.lean`);
* `etaIota`: its conclusion asks the η bit, unset at the step; its hypotheses are refuted. They
  observe `block_is_multi` answering `0` at the loaded block (two or more inductives: refused by
  that function's specification, `multi_not_zero_core`), so the loaded inductive is the only
  member of the family's block, with no index and one constructor; and they observe the
  recursion scan `struct_is_rec` answering other than `1` at it, which a modeled block of one
  inductive refutes (`struct_is_rec_one`, `FamilyAlias/StructRecScan.lean`: the dispatch's nested
  occurrence is in a field that mentions the member).

Two more hold from the seam `FamilyMembersCanon` (the family check stores each new inductive and
constructor in the canonical annotated form the circuit loads, `LoadedReads.canonAnn` of its
reading, and the block's used references are stored): `getIprj` and `getCprj`, through the
stored constants' shapes (`FamLoadCtx.indForm`, `ctorForm`) and the canonical loads
(`LoadedReads.get_ci_iprj_load_canon`, `get_ci_cprj_load_canon`).

The last one, `getCI` (the load of a new constant at its key), holds from the same seam: at an
inductive or a constructor projection (`FamLoadCtx.getCI_iprj`, `getCI_cprj`: the load's trace
bounds the record's indices, `LoadedReads.get_ci_iprj_canon`, `get_ci_cprj_canon`), and at a
recursor projection of the family record, where the seam gives the stored recursor's loaded form
(`TwinFamily.TwinMemberLoaded`) and the family record's references stored
(`FamLoadCtx.getCI_rprj`: `LoadedReads.get_ci_rprj_canon`, then `ciRep_recr_rules` for the
rules' install bits). -/

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

/-- **The load fact at a recursor projection of the family record**, as the family check would
give it directly: the load of a new constant at its key where the address holds a recursor
projection record. `FamLoadCtx.newLoads` no longer reads it (`FamLoadCtx.getCI_rprj`). -/
structure FamilyLoadsCheck (c : ScopedCtx) (new : List (ConstantInfo .anon)) : Prop where
  getCI : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Good c.toCtx cs →
    Bytes.RepAddressRef addrTy h a addr → (∃ cn ∈ new, cn.name = keyOf c.t (ixAddr a)) →
    (∃ (cm : Ixon.Constant) (p : Ixon.RecursorProj),
      IxVM.Consistency.recordOf c.E (ixAddr a) = some cm ∧ cm.info = .rPrj p) →
      ∃ ci, c.env.find? (c.κ (ixAddr a)) = some ci ∧ CIPtrRep c.κ h' ptr ci

end Check

/-! ## What the step's store and records give -/

section
open IxVM.Consistency

/-- **The circuit loads each new constant of the family step in its canonical annotated form**
(the seam of the loads; the family check stores what it loads). At the environment `env` after
the step: the references the block `cb` (members `ms`, at `A`) and the family record `crb`
(members `rs`, at `rb`) use are stored; each inductive member and each of its constructors, read
over the store `E₀`'s blobs as `ty₀` and stored at its key, has a closed reading with its level
parameters defined, and its stored type is the canonical annotation of the reading at the
member's root (`LoadedReads.canonAnn`); each recursor member of the family record, read as a
recursor and stored at its key, is loaded as the stored recursor (`TwinFamily.TwinMemberLoaded`).
The stored constant's kind, name, level parameters and counts are the reading's (`StoredAs`),
not part of the seam. -/
structure FamilyMembersCanon (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (A : _root_.Address)
    (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (rb : _root_.Address) (crb : Ixon.Constant)
    (rs : Array Ixon.MutConst) (env : Ix.Kernel.Env .anon) : Prop where
  /-- The references the block uses are stored. Producer: open. The walk gives, at the
  top-walked block, the inert clause (`Claim.TopWalkCore.inertClause`) and `NeedOk` of each
  uncovered used reference (`Claim.TopWalk.need`); a covered one is stored by the witness's
  environment (`coverAt_of_graph`). With the step's need hypothesis (a needed reference is stored
  or a family address) and the family addresses stored after the step, that gives this field;
  the load fields' binders do not receive the need hypothesis today. -/
  used : Decl.UsedRefsStored t env cb
  /-- Each inductive member is stored in the canonical annotated form of its reading. Producer:
  the circuit side; the family check's load of the member (`Ingress::get_ci_iprj`), which stores
  what it loads. -/
  ind : ∀ (i : Nat) (ind : Ixon.Inductive) (ty₀ : Ix.Kernel.Expr .anon) (cv : ConstantVal .anon)
      (caps : IndCaps .anon), i < UInt64.size → ms[i]? = some (.indc ind) →
    (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t A ms)).read ind.typ = .ok ty₀ →
    env.find? (Core.keyOf t (Core.iprjAddr A i)) = some (.indInfo cv caps) →
    ty₀.looseBVarsBounded 0 = true ∧
      ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧
      LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
        ((L1.mutsRootOffset ms.toList i : Nat) : F) ind.typ ty₀ = some cv.type
  /-- Each constructor is stored in the canonical annotated form of its reading. Producer: the
  circuit side; the family check's load of the constructor (`Ingress::get_ci_cprj`), which stores
  what it loads. -/
  ctor : ∀ (i : Nat) (ind : Ixon.Inductive) (j : Nat) (ct : Ixon.Constructor)
      (ty₀ : Ix.Kernel.Expr .anon) (cv : ConstantVal .anon) (nP nF : Nat),
    i < UInt64.size → j < UInt64.size → ms[i]? = some (.indc ind) → ind.ctors[j]? = some ct →
    (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t A ms)).read ct.typ = .ok ty₀ →
    env.find? (Core.keyOf t (Core.cprjAddr A i j)) = some (.ctorInfo cv nP nF) →
    ty₀.looseBVarsBounded 0 = true ∧
      ty₀.allLevelParamsDefined (List.range ct.lvls.toNat) = true ∧
      LoadedReads.canonAnn cb (List.range ct.lvls.toNat)
        (((L1.mutsRootOffset ms.toList i : Nat) : F) + 1 + ((j : Nat) : F)) ct.typ ty₀ =
        some cv.type
  /-- The references the family record uses are stored. Producer: open. No walk reaches the
  family record: the family check would have to assert, at each reference its recursors use,
  what the walk asserts of a walked record's (the reference allowed, no block, the record and its
  owner safe), which gives its inert clause and `NeedOk`; with the step's need hypothesis and the
  family addresses stored after the step, that gives this field. -/
  usedRecs : Decl.UsedRefsStored t env crb
  /-- Each recursor member of the family record, read as the recursor `cv` (rules `rules₀`) and
  stored at its key as `cv'` (rules `rules'`), is loaded as the stored recursor: the reading's
  level count, scope and K clause, the stored type the canonical annotation of the read type at
  the member's root, the stored rules the canonical rules' field counts and right-hand sides
  (`TwinFamily.TwinMemberLoaded`). Producer: the circuit side; the family check's load of the
  recursor (`Ingress::get_ci` at its projection record), which stores what it loads. -/
  recLoaded : ∀ (p : Ixon.RecursorProj) (rc : Ixon.Recursor) (cv : ConstantVal .anon)
      (mI rP : Nat) (rules₀ : List (Ix.Kernel.RecRule .anon)) (cv' : ConstantVal .anon)
      (mI' rP' : Nat) (rules' : List (Ix.Kernel.RecRule .anon)),
    p.block = rb → rs[p.idx.toNat]? = some (.recr rc) →
    RecReads t (recordOf E₀) (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs)
      (keyOf t (memberAddr rb p.idx.toNat (.recr rc))) rc (.recInfo cv mI rP rules₀) →
    env.find? (keyOf t (memberAddr rb p.idx.toNat (.recr rc))) =
      some (.recInfo cv' mI' rP' rules') →
    TwinFamily.TwinMemberLoaded crb rs p rc cv.levelParams cv.type rules₀ cv' rules'

/-- **What the family step gives the load facts**, at the prefix context `C` and the new constants
`new`: a well-formed table, a decoded store that holds a hashed block's projection records, the
block `cb` (members `ms`) at `A` and the family record `crb` (members `rs`) at `rb` with their
projection records, the route fact at `A`, every new constant at the key of a constant address of
the two records or a definition at a derived key, and every such address stored; at a block of
one inductive, the first constructor stored with the record's counts, and a field in it where
the member has no index and one constructor; the stored forms of the members, constructors and
recursors, and the references the two records use stored. -/
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
  /-- The dispatch at the block answers `1` at the store. -/
  routeTrue : Route.blockRoute C.E A = some true
  /-- At a block of one inductive, each constructor's stored type, read as the dispatch reads it,
  is a telescope of its parameters and fields into a constant applied to `params + indices`
  arguments, the first `params` of them atoms; its parameter count is the member's (the walk's
  return-type check, `modeledCtor_trees`). -/
  ctorTrees : ∀ ind, ms = #[.indc ind] → ∀ j < ind.ctors.size,
    ∃ (ct : Ixon.Constructor) (T Bd : Route.ScanTree),
      ind.ctors[j]? = some ct ∧ ct.params.toNat = ind.params.toNat ∧
      Route.ExprTree cb.refs.toList
        (L1.blockRecurAddrs A (#[.indc ind] : Array Ixon.MutConst).toList)
        cb.sharing.toList 4294967295 ct.typ T ∧
      T.peel (ct.params.toNat + ct.fields.toNat) = some Bd ∧ (∃ a, Bd.head = .const a) ∧
      Bd.args.length = ct.params.toNat + ind.indices.toNat ∧
      ∀ k < ct.params.toNat, Bd.args[k]? = some .atom
  /-- The registry's facts at the prefix context. -/
  core : Core.ScopedCoreFacts (Core.Ctx.stored C)
  /-- The role table checks. -/
  check : C.t.check = .ok ()
  /-- The references the block uses are stored after the step. -/
  used : Decl.UsedRefsStored C.t (appCtx C new).env cb
  /-- Each inductive member is stored at its key as the canonical constant of its reading. -/
  indForm : ∀ i ind, i < UInt64.size → ms[i]? = some (.indc ind) →
    ∃ (ty₀ ty' : Ix.Kernel.Expr .anon) (caps : IndCaps .anon),
      (exprReader C.t (fun x => C.E.blobs.get? x) cb id (blockSelf C.t A ms)).read ind.typ =
        .ok ty₀ ∧
      ty₀.looseBVarsBounded 0 = true ∧
      ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧
      LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
        ((L1.mutsRootOffset ms.toList i : Nat) : F) ind.typ ty₀ = some ty' ∧
      (appCtx C new).env.find? (Core.keyOf C.t (Core.iprjAddr A i)) =
        some (.indInfo ⟨Core.keyOf C.t (Core.iprjAddr A i), List.range ind.lvls.toNat, ty'⟩ caps)
  /-- Each constructor is stored at its key as the canonical constant of its reading. -/
  ctorForm : ∀ i ind j ct, i < UInt64.size → j < UInt64.size → ms[i]? = some (.indc ind) →
    ind.ctors[j]? = some ct → ct.cidx.toNat = j ∧
    ∃ (ty₀ ty' : Ix.Kernel.Expr .anon),
      (exprReader C.t (fun x => C.E.blobs.get? x) cb id (blockSelf C.t A ms)).read ct.typ =
        .ok ty₀ ∧
      ty₀.looseBVarsBounded 0 = true ∧
      ty₀.allLevelParamsDefined (List.range ct.lvls.toNat) = true ∧
      LoadedReads.canonAnn cb (List.range ct.lvls.toNat)
        (((L1.mutsRootOffset ms.toList i : Nat) : F) + 1 + ((j : Nat) : F)) ct.typ ty₀ =
        some ty' ∧
      (appCtx C new).env.find? (Core.keyOf C.t (Core.cprjAddr A i j)) =
        some (.ctorInfo ⟨Core.keyOf C.t (Core.cprjAddr A i j), List.range ct.lvls.toNat, ty'⟩
          ct.params.toNat ct.fields.toNat)
  /-- The family record at its address. -/
  rrecord : recordOf C.E rb = some crb
  /-- The references the family record uses are stored after the step. -/
  usedRecs : Decl.UsedRefsStored C.t (appCtx C new).env crb
  /-- Each recursor member of the family record is stored at its key with its reading's level
  parameters and counts, the canonical annotation of its read type, and rules with the field
  counts and right-hand sides of its canonical rules (`TwinFamily.TwinMemberLoaded`). -/
  recForm : ∀ (p : Ixon.RecursorProj) (rc : Ixon.Recursor), p.block = rb →
    rs[p.idx.toNat]? = some (.recr rc) →
    ∃ (ps : List Ix.Kernel.LevelParam) (ty₀ : Ix.Kernel.Expr .anon)
      (rules₀ : List (Ix.Kernel.RecRule .anon)) (cv' : ConstantVal .anon)
      (rules' : List (Ix.Kernel.RecRule .anon)),
      ps.Perm (List.range ps.length) ∧
      (exprReader C.t (fun x => C.E.blobs.get? x) crb (Ix.Kernel.Reader.recParam ps)
        (blockSelf C.t rb rs)).read rc.typ = .ok ty₀ ∧
      List.Forall₂ (fun (ru : Ixon.RecursorRule) (rl₀ : Ix.Kernel.RecRule .anon) =>
        rl₀.nfields = ru.fields.toNat ∧
        (exprReader C.t (fun x => C.E.blobs.get? x) crb (Ix.Kernel.Reader.recParam ps)
          (blockSelf C.t rb rs)).read ru.rhs = .ok rl₀.rhs) rc.rules.toList rules₀ ∧
      TwinFamily.TwinMemberLoaded crb rs p rc ps ty₀ rules₀ cv' rules' ∧
      (appCtx C new).env.find? (Core.keyOf C.t (Core.rprjAddr rb p.idx.toNat)) =
        some (.recInfo ⟨Core.keyOf C.t (Core.rprjAddr rb p.idx.toNat), ps, cv'.type⟩
          (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
          (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rules')

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

/-- **A block a run decodes from bytes hashed to the family's block address is the family's
record**, where the run hashes no collision with the store. -/
theorem FamLoadCtx.block_eq (hL : FamLoadCtx C new A cb ms rb crb rs) {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := C.E } [] cs) {blkBytes : ByteArray}
    (hh : Hashed cs blkBytes) (ha : Address.blake3Pure blkBytes = A) {cb' : Ixon.Constant}
    (hex : Ixon.deConstantExact blkBytes = .ok cb') : cb' = cb := by
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hL.record
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hnc blkBytes hh ha
  rw [hbB, hdecB] at hex
  exact (Except.ok.inj hex).symm

/-- **The family's block is stored after the step**: every member address is a family address. -/
theorem FamLoadCtx.blockStored (hL : FamLoadCtx C new A cb ms rb crb rs) :
    LoadedReads.BlockStored C.t (appCtx C new).env A ms := by
  intro y hy
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hy
  obtain ⟨m, hm, hye⟩ := LoadedReads.blockRecurAddrs_get hk
  exact hL.found y (Or.inl (Or.inr ⟨ms, k, m, hL.muts, hm, Or.inl hye⟩))

/-- **A load of a new inductive at its constant address represents the stored inductive**: the
load reads the member's projection record and, through it, the family's block (its trace bounds
the record's member index); the member at that index is stored at its key as the canonical
constant of its reading (`FamLoadCtx.indForm`), which the load represents
(`LoadedReads.get_ci_iprj_canon` at the environment after the step). -/
theorem FamLoadCtx.getCI_iprj (hL : FamLoadCtx C new A cb ms rb crb rs)
    {addr ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {a : Bytes.Address}
    (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs) (good : Core.Good (appCtx C new) cs)
    (ha : Bytes.RepAddressRef Core.addrTy h a addr) {i : Nat} {ind : Ixon.Inductive}
    (hget : ms[i]? = some (.indc ind)) (hx : Core.ixAddr a = memberAddr A i (.indc ind)) :
    ∃ ci, (appCtx C new).env.find? ((appCtx C new).stored.κ (Core.ixAddr a)) = some ci ∧
      Core.CIPtrRep (appCtx C new).stored.κ h' ptr ci := by
  have hrec : recordOf C.E (Core.ixAddr a) = some (memberProjection A i (.indc ind)) := by
    rw [hx]
    exact hL.members i _ hget
  have hinfo : (memberProjection A i (.indc ind)).info = .iPrj ⟨i.toUInt64, A⟩ := rfl
  -- the member at the record's index, bounded, from the load's trace
  obtain ⟨rawBytes, c', hh, haddr, hex, -, hres⟩ := L1.get_ci_block_trace_spec good.2 ha ev
  obtain ⟨lc, hgetc, hdec⟩ := LoadedReads.recordOf_inv hrec
  have hb : rawBytes = lc.rawBytes := Core.load_escape hgetc good.1 rawBytes hh haddr
  have hc : c' = memberProjection A i (.indc ind) := by
    rw [hb, hdec] at hex
    exact (Except.ok.inj hex).symm
  have hinfo' : c'.info = .iPrj ⟨i.toUInt64, A⟩ := (congrArg Ixon.Constant.info hc).trans hinfo
  unfold L1.GetCIBlockTraceResult at hres
  rw [hinfo'] at hres
  obtain ⟨hidx, blkBytes, cb', ms', ind', _, _, _, _, hhB, haB, hexB, hcb', hms', -⟩ := hres
  rw [hL.block_eq good.1 hhB haB hexB] at hcb'
  have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hL.muts)
  rw [e2] at hms'
  have hi64 : i.toUInt64.toNat < UInt64.size := Nat.lt_trans hidx (by decide)
  have hm' : ms[i.toUInt64.toNat]? = some (.indc ind') := by
    rw [← Array.getElem?_toList]
    exact hms'
  -- the stored member and the load's canonical constant
  obtain ⟨ty₀, ty', caps, hty, hlbb, hdef, hcan, hfind⟩ := hL.indForm _ ind' hi64 hm'
  obtain ⟨haddr', ty'', hcT, -, -, hrepS⟩ := LoadedReads.get_ci_iprj_canon hL.check good.1 good.2
    ha ev hrec hinfo hL.record hL.muts hm' hty hlbb hdef
  have e3 : ty'' = ty' := Option.some.inj (hcT.symm.trans hcan)
  have hxa : Core.ixAddr a = Core.iprjAddr A i.toUInt64.toNat := haddr'
  have hrep := hrepS (appCtx C new).env C.lim hL.used hL.blockStored caps
  rw [e3, hxa] at hrep
  rw [hxa, Core.Ctx.stored_key_of_find (c := appCtx C new) hfind]
  exact ⟨_, hfind, hrep⟩

/-- **A load of a new constructor at its constant address represents the stored constructor**:
the load reads the constructor's projection record and, through it, the family's block (its
trace bounds the record's member and constructor indices and gives the constructor at them); it
is stored at its key as the canonical constant of its reading (`FamLoadCtx.ctorForm`), which the
load represents (`LoadedReads.get_ci_cprj_canon` at the environment after the step). -/
theorem FamLoadCtx.getCI_cprj (hL : FamLoadCtx C new A cb ms rb crb rs)
    {addr ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {a : Bytes.Address}
    (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs) (good : Core.Good (appCtx C new) cs)
    (ha : Bytes.RepAddressRef Core.addrTy h a addr) {i j : Nat} {ind : Ixon.Inductive}
    (hget : ms[i]? = some (.indc ind)) (hj : j < ind.ctors.size)
    (hx : Core.ixAddr a = ctorAddr A i j) :
    ∃ ci, (appCtx C new).env.find? ((appCtx C new).stored.κ (Core.ixAddr a)) = some ci ∧
      Core.CIPtrRep (appCtx C new).stored.κ h' ptr ci := by
  have hrec : recordOf C.E (Core.ixAddr a) = some (constructorProjection A i j) := by
    rw [hx]
    exact hL.ctors i ind j hget hj
  have hinfo : (constructorProjection A i j).info = .cPrj ⟨i.toUInt64, j.toUInt64, A⟩ := rfl
  -- the member and constructor at the record's indices, bounded, from the load's trace
  obtain ⟨rawBytes, c', hh, haddr, hex, -, hres⟩ := L1.get_ci_block_trace_spec good.2 ha ev
  obtain ⟨lc, hgetc, hdec⟩ := LoadedReads.recordOf_inv hrec
  have hb : rawBytes = lc.rawBytes := Core.load_escape hgetc good.1 rawBytes hh haddr
  have hc : c' = constructorProjection A i j := by
    rw [hb, hdec] at hex
    exact (Except.ok.inj hex).symm
  have hinfo' : c'.info = .cPrj ⟨i.toUInt64, j.toUInt64, A⟩ :=
    (congrArg Ixon.Constant.info hc).trans hinfo
  unfold L1.GetCIBlockTraceResult at hres
  rw [hinfo'] at hres
  obtain ⟨hidx, hcidx, blkBytes, cb', ms', ind', ct', _, _, _, _, hhB, haB, hexB, hcb', hms',
    hcts, -⟩ := hres
  rw [hL.block_eq good.1 hhB haB hexB] at hcb'
  have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hL.muts)
  rw [e2] at hms'
  have hi64 : i.toUInt64.toNat < UInt64.size := Nat.lt_trans hidx (by decide)
  have hj64 : j.toUInt64.toNat < UInt64.size := Nat.lt_trans hcidx (by decide)
  have hm' : ms[i.toUInt64.toNat]? = some (.indc ind') := by
    rw [← Array.getElem?_toList]
    exact hms'
  have hct : ind'.ctors[j.toUInt64.toNat]? = some ct' := by
    rw [← Array.getElem?_toList]
    exact hcts
  -- the stored constructor and the load's canonical constant
  obtain ⟨hcj, ty₀, ty', hty, hlbb, hdef, hcan, hfind⟩ :=
    hL.ctorForm _ ind' _ ct' hi64 hj64 hm' hct
  obtain ⟨haddr', ty'', hcT, -, -, hrepS⟩ := LoadedReads.get_ci_cprj_canon hL.check good.1 good.2
    ha ev hrec hinfo hL.record hL.muts hm' hct hcj hty hlbb hdef
  have e3 : ty'' = ty' := Option.some.inj (hcT.symm.trans hcan)
  have hxa : Core.ixAddr a = Core.cprjAddr A i.toUInt64.toNat j.toUInt64.toNat := haddr'
  have hself : ∃ ci, (appCtx C new).env.find? (Core.keyOf C.t (Core.ixAddr a)) = some ci := by
    rw [hxa]
    exact ⟨_, hfind⟩
  have hrep := hrepS (appCtx C new).env C.lim hL.used hL.blockStored hself
  rw [e3, hxa] at hrep
  rw [hxa, Core.Ctx.stored_key_of_find (c := appCtx C new) hfind]
  exact ⟨_, hfind, hrep⟩

/-- **The family record's block is stored after the step**: every member address is a family
address. -/
theorem FamLoadCtx.rblockStored (hL : FamLoadCtx C new A cb ms rb crb rs) :
    LoadedReads.BlockStored C.t (appCtx C new).env rb rs := by
  intro y hy
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hy
  obtain ⟨m, hm, hye⟩ := LoadedReads.blockRecurAddrs_get hk
  exact hL.found y (Or.inr (Or.inr ⟨rs, k, m, hL.rmuts, hm, Or.inl hye⟩))

/-- **A load of a new recursor at its constant address represents the stored recursor**: the
load reads the member's projection record and, through it, the family record (its trace gives
the recursor at the record's member index); that recursor is stored at its key with the reading's
level parameters and counts, the canonical annotation of its read type and rules agreeing with
its canonical rules on field counts and right-hand sides (`FamLoadCtx.recForm`); the load
represents the canonical constant (`LoadedReads.get_ci_rprj_canon` at the environment after the
step), and so the stored one (`ciRep_recr_rules`). -/
theorem FamLoadCtx.getCI_rprj (hL : FamLoadCtx C new A cb ms rb crb rs)
    {addr ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {a : Bytes.Address}
    (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs) (good : Core.Good (appCtx C new) cs)
    (ha : Bytes.RepAddressRef Core.addrTy h a addr) {i : Nat} {r : Ixon.Recursor}
    (hget : rs[i]? = some (.recr r)) (hx : Core.ixAddr a = memberAddr rb i (.recr r)) :
    ∃ ci, (appCtx C new).env.find? ((appCtx C new).stored.κ (Core.ixAddr a)) = some ci ∧
      Core.CIPtrRep (appCtx C new).stored.κ h' ptr ci := by
  have hrec : recordOf C.E (Core.ixAddr a) = some (memberProjection rb i (.recr r)) := by
    rw [hx]
    exact hL.rmembers i _ hget
  have hinfo : (memberProjection rb i (.recr r)).info = .rPrj ⟨i.toUInt64, rb⟩ := rfl
  -- the recursor at the record's index, from the load's trace
  obtain ⟨rawBytes, c', hh, haddr, hex, -, hres⟩ := L1.get_ci_block_trace_spec good.2 ha ev
  obtain ⟨lc, hgetc, hdec⟩ := LoadedReads.recordOf_inv hrec
  have hb : rawBytes = lc.rawBytes := Core.load_escape hgetc good.1 rawBytes hh haddr
  have hc : c' = memberProjection rb i (.recr r) := by
    rw [hb, hdec] at hex
    exact (Except.ok.inj hex).symm
  have hinfo' : c'.info = .rPrj ⟨i.toUInt64, rb⟩ := (congrArg Ixon.Constant.info hc).trans hinfo
  unfold L1.GetCIBlockTraceResult at hres
  rw [hinfo'] at hres
  obtain ⟨-, blkBytes, cb', rs', rc', _, _, _, hhB, haB, hexB, hcb', hms', -⟩ := hres
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hL.rrecord
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB good.1 blkBytes hhB haB
  rw [hbB, hdecB] at hexB
  have e1 : cb' = crb := (Except.ok.inj hexB).symm
  rw [e1] at hcb'
  have e2 : rs' = rs := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hL.rmuts)
  rw [e2] at hms'
  have hm' : rs[i.toUInt64.toNat]? = some (.recr rc') := by
    rw [← Array.getElem?_toList]
    exact hms'
  -- the stored recursor and the load's canonical constant
  obtain ⟨ps, ty₀, rules₀, cv', rules', hperm, hty, hrules₀, hML, hfind⟩ :=
    hL.recForm ⟨i.toUInt64, rb⟩ rc' rfl hm'
  have hrules : List.Forall₂ (fun (ru : Ixon.RecursorRule) (rl₀ : Ix.Kernel.RecRule .anon) =>
      rl₀.nfields = ru.fields.toNat ∧
      (exprReader C.t (fun x => C.E.blobs.get? x) crb (Ix.Kernel.Reader.recParam ps)
        (blockSelf C.t rb rs)).read ru.rhs = .ok rl₀.rhs ∧
      rl₀.rhs.looseBVarsBounded 0 = true ∧ rl₀.rhs.allLevelParamsDefined ps = true)
      rc'.rules.toList rules₀ :=
    TwinFamily.lforall₂_mono (fun ru rl₀ h => ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩)
      (TwinFamily.lforall₂_and_mem hrules₀ hML.rulesScoped)
  obtain ⟨haddr', ty', rls, hcT, hcR, -, -, -, hrepS⟩ := LoadedReads.get_ci_rprj_canon hL.check
    good.1 good.2 ha ev hrec hinfo hL.rrecord hL.rmuts hm' hML.lvls hperm hty hML.tyBounded
    hML.tyLevels hrules hML.kOne
  obtain ⟨rls₂, hcR₂, hagree, hK⟩ := hML.rules
  have e4 : rls = rls₂ := Option.some.inj (hcR.symm.trans hcR₂)
  rw [← e4] at hagree hK
  have e3 : ty' = cv'.type := Option.some.inj (hcT.symm.trans hML.ty)
  obtain ⟨v, hld, hv⟩ := hrepS (appCtx C new).env C.lim hL.usedRecs hL.rblockStored
  have hv' := ciRep_recr_rules hv hagree hK
  have hxa : Core.ixAddr a = Core.rprjAddr rb i.toUInt64.toNat := haddr'
  have hfind' : (appCtx C new).env.find? (Core.keyOf C.t (Core.rprjAddr rb i.toUInt64.toNat)) =
      some (.recInfo ⟨Core.keyOf C.t (Core.rprjAddr rb i.toUInt64.toNat), ps, cv'.type⟩
        (rc'.params.toNat + rc'.motives.toNat + rc'.minors.toNat + rc'.indices.toNat)
        (rc'.params.toNat + rc'.motives.toNat + rc'.minors.toNat) rules') := hfind
  rw [e3, hxa] at hv'
  rw [hxa, Core.Ctx.stored_key_of_find (c := appCtx C new) hfind']
  exact ⟨_, hfind', ⟨v, hld, hv'⟩⟩

/-- **At a block of two or more inductives no good run answers `block_is_multi = 0`**, at the
registry's facts of the prefix context (`multi_not_zero`, read from the facts alone). -/
theorem multi_not_zero_core {C : Core.Ctx} (core : Core.ScopedCoreFacts (Core.Ctx.stored C))
    {B : _root_.Address} (hm : MultiAt C.E B) {bq : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} {bb : Bytes.Address}
    (ev : ObsFn Core.W "KernelModeled::block_is_multi" [bq] h (.field 0) h' cs)
    (hnc : ¬ View.HashedCollision { env := C.E } [] cs) (hbd : Bounded cs)
    (hrep : Bytes.RepAddressRef Core.addrTy h bb bq) (hB : Core.ixAddr bb = B) : False := by
  obtain ⟨cb, ms, hrec, hms, h2⟩ := hm
  have hspec := Core.Registry.spec _ (Core.scoped_steps _ core) _ _ _ _ _ _ ev
    (.callees .block_is_multi) rfl
  have h1 := ((hspec bq bb rfl ⟨hnc, hbd, fun _ _ => trivial⟩ hrep).2 cb
    (by rw [hB]; exact hrec)).2 ⟨ms, hms, h2⟩
  exact absurd (Value.field.inj h1) (by decide)

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
  getCI := by
    intro addr ptr h h' cs a ev good ha hn
    obtain ⟨cn, hcn, hname⟩ := hn
    rcases hL.newName cn hcn with ⟨x, hx, hx'⟩ | ⟨-, n, d, hnd⟩
    · have hax : Core.ixAddr a = x := Core.keyOf_inj hL.wf (hname.symm.trans hx')
      rcases hx with ⟨⟨-, hs⟩ | ⟨ms', i, m, hinfo', hget, hxm | ⟨ind, j, hind, hj, hxc⟩⟩⟩ |
          ⟨⟨-, hs⟩ | ⟨rs', i, m, hinfo', hget, hxm | ⟨ind, j, hind, hj, hxc⟩⟩⟩
      · exact (standalone_not_block hs ⟨ms, hL.muts⟩).elim
      · have e : ms' = ms := Ixon.ConstantInfo.muts.inj (hinfo'.symm.trans hL.muts)
        rw [e] at hget
        obtain ⟨ind, rfl⟩ := hL.indcs m (by simpa using Array.mem_of_getElem? hget)
        exact hL.getCI_iprj ev good ha hget (hax.trans hxm)
      · have e : ms' = ms := Ixon.ConstantInfo.muts.inj (hinfo'.symm.trans hL.muts)
        rw [e, hind] at hget
        exact hL.getCI_cprj ev good ha hget hj (hax.trans hxc)
      · exact (standalone_not_block hs ⟨rs, hL.rmuts⟩).elim
      · have e : rs' = rs := Ixon.ConstantInfo.muts.inj (hinfo'.symm.trans hL.rmuts)
        rw [e] at hget
        obtain ⟨r, rfl⟩ := hL.recrs m (by simpa using Array.mem_of_getElem? hget)
        exact hL.getCI_rprj ev good ha hget (hax.trans hxm)
      · have e : rs' = rs := Ixon.ConstantInfo.muts.inj (hinfo'.symm.trans hL.rmuts)
        rw [e] at hget
        obtain ⟨r, hr⟩ := hL.recrs m (by simpa using Array.mem_of_getElem? hget)
        rw [hind] at hr
        exact nomatch hr
    · exact (keyOf_nonAux C.t (Core.ixAddr a) n d (hname.symm.trans hnd)).elim
  getCprj := by
    intro bp ptr i j h h' cs b ev hfam good hb
    have hbh := L1.hashedBlockAt_of_get_ci_cprj good hb ev
    have hbA := hL.famNew_block hbh hfam
    subst hbA
    obtain ⟨-, -, -, blkBytes, cb', ms', ind, ct, blobs, v, hhB, haB, hexB, -, hcb', hms', hct',
      -, -, -⟩ := L1.get_ci_cprj_spec good.2 hb ev
    have e1 : cb' = cb := hL.block_eq good.1 hhB haB hexB
    subst e1
    have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hL.muts)
    subst e2
    have hmem : ms'[ZMod.val i]? = some (.indc ind) := by
      rw [← Array.getElem?_toList]
      exact hms'
    have hct : ind.ctors[ZMod.val j]? = some ct := by
      rw [← Array.getElem?_toList]
      exact hct'
    obtain ⟨hcidx, ty₀, ty', hty, hlbb, hdef, hcan, hfind⟩ :=
      hL.ctorForm (ZMod.val i) ind (ZMod.val j) ct (val_lt_uint64 i) (val_lt_uint64 j) hmem hct
    obtain ⟨ty'', hcT, -, -, hrepS⟩ := LoadedReads.get_ci_cprj_load_canon hL.check good.1 good.2
      hb ev hL.record hL.muts hmem hct hcidx hty hlbb hdef
    have e3 : ty'' = ty' := Option.some.inj (hcT.symm.trans hcan)
    subst e3
    have hrep := hrepS (appCtx C new).env C.lim hL.used hL.blockStored ⟨_, hfind⟩
    refine ⟨⟨_, hrep⟩, ?_⟩
    intro cv nP nF hf
    rw [Core.Ctx.stored_key_of_find (c := appCtx C new) hfind] at hf
    have hf' := hf.symm.trans hfind
    rw [Option.some.inj hf']
    exact hrep
  getIprj := by
    intro bp ptr i h h' cs b ev hfam good hb
    have hbh := L1.hashedBlockAt_of_get_ci_iprj good hb ev
    have hbA := hL.famNew_block hbh hfam
    subst hbA
    obtain ⟨-, -, blkBytes, cb', ms', ind, blobs, v, hhB, haB, hexB, -, hcb', hms', -, -, -⟩ :=
      L1.get_ci_iprj_spec good.2 hb ev
    have e1 : cb' = cb := hL.block_eq good.1 hhB haB hexB
    subst e1
    have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hL.muts)
    subst e2
    have hmem : ms'[ZMod.val i]? = some (.indc ind) := by
      rw [← Array.getElem?_toList]
      exact hms'
    obtain ⟨ty₀, ty', caps, hty, hlbb, hdef, hcan, hfind⟩ :=
      hL.indForm (ZMod.val i) ind (val_lt_uint64 i) hmem
    obtain ⟨ty'', hcT, -, -, hrepS⟩ := LoadedReads.get_ci_iprj_load_canon hL.check good.1 good.2
      hb ev hL.record hL.muts hmem hty hlbb hdef
    have e3 : ty'' = ty' := Option.some.inj (hcT.symm.trans hcan)
    subst e3
    refine ⟨_, ?_, hrepS (appCtx C new).env C.lim hL.used hL.blockStored caps⟩
    rw [Core.Ctx.stored_key_of_find (c := appCtx C new) hfind]
    exact hfind
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
  etaIota := by
    intro pp ptr nl ty u blk h1 h2 cs1 pa b i m cvT cvc caps cnP cnF us l ev good hpa hld hb hT hC
      hmulti hrec hpi hnz hm
    exfalso
    have hfew : Core.FewInductives (appCtx C new) (Core.ixAddr b) := by
      intro cst ms' hrecB hms'
      obtain ⟨bq, h3, h4, cs3, evM, goodM, hbq⟩ := hmulti
      by_contra hlt
      exact multi_not_zero_core hL.core ⟨cst, ms', hrecB, hms', by omega⟩ evM goodM.1 goodM.2
        hbq rfl
    obtain ⟨hbA, hval, ind, hms, hxa⟩ := hL.member_of_load ev good hpa hld hb
      (hm.imp (fun hm => ⟨cvT, caps, hT, hm⟩) (fun hm => ⟨cvc, cnP, cnF, hC, hm⟩)) hfew
    obtain ⟨hidx, hsz⟩ := hL.member_counts hms ev good hpa hld hxa
    rw [ZMod.val_zero] at hidx
    rw [ZMod.val_one] at hsz
    have hmuts : cb.info = .muts #[.indc ind] := by
      rw [← hms]
      exact hL.muts
    have hproj : recordOf C.E (Core.iprjAddr A 0) = some (memberProjection A 0 (.indc ind)) :=
      hL.members 0 (.indc ind) (by subst hms; rfl)
    obtain ⟨sp, v, h5, h6, cs5, evR, hne, goodR, hpR⟩ := hrec
    exact struct_is_rec_one hL.core hL.decoded hL.record hmuts hproj hL.routeTrue hidx.symm
      hsz.symm (hL.ctorTrees ind hms 0 (by omega)) evR hne ⟨goodR.1, goodR.2⟩ hpR hxa
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
