import IxVMRefinement.Binding.FamilyCallPremises
import IxVMRefinement.Binding.FamilyReconMinors
import IxVMRefinement.Binding.FamilyReconRules
import IxVMRefinement.Binding.FamilyFlatWalk
import IxVMRefinement.Binding.FamilyFlatBuild
import IxVMRefinement.Guard.RunStoreReading

/-! # The load answers of a family call

The leaf specifications of the reconstruction and of the flattening read the run's store through
single-call predicates. This module produces the ones `FamilyReconAnswers` leaves, packages all of
them for one call list, and reduces their level premises, for a selected family's check, to which
addresses the check loads.

* A constructor's load. `ctorRecord_of_load`: an `Ingress::get_ci_cprj` of a run, at a block and
  positions whose constructor reading mentions only its level parameters
  (`CtorLevelsDefinedAt`), loads a `Ctor` of the store's block record, its type represented
  exactly as the open loaded form. From it `ctorAnswers_of_run` (`CtorAnswers`),
  `cprjAnswers_of_run` (`CprjAnswers`, at the store's field count `ctorFieldsAt`, a function:
  `ctorFieldsAt_unique`) and `flatCtorAnswersIn_of_run` (`FlatCtorAnswersIn`). The first two ask
  the level premise of the constructors the calls load (`CprjLevelsDefined`), the third of the
  blocks of its set.
* `ctorAddrAnswers_of_run` (`CtorAddrAnswers`): `KernelCheck::projection_addr_ctor` computes the
  constructor's constant address; every key of a table's keying resolves (`resolved_keyOf`).
* `flat_originals_walk_addrs`, `build_flat_originals_addrs`, `flatMembersAnswersIn_of_run`
  (`FlatMembersAnswersIn`): `KernelCheck::build_flat_originals` lists a block's inductive
  members' addresses, with no premise on level counts or the offset.
* For a part `root` of a run, with the level premises asked of `root` alone: `defnAnswers_of_sub`,
  `indAnswers_of_sub`, `guardDefnAnswers_of_sub`, `CtorOfAnswers.mono`, `ModeledAnswers.mono`.
* **`FamilyCallAnswers t E cs S`**: every answer for the calls `cs`, with the keying's facts;
  `familyCallAnswers_of_sub` and **`familyCallAnswers`** (the calls of an observed
  `KernelModeled::check_family`) give it from `LoadedLevelsDefined` and `CprjLevelsDefined` of
  `cs` and `CtorLevelsDefinedAt` on `S`.
* The store after the group of a selected family. `selected_payload_reach`: the family record is
  reached through the group's payload, the block's record taken from the family check, so no
  family clause of the run is asked. `SelectedStore`, `selectedStore_of_run`: that store holds
  the block, its members' and constructors' projection records, the family record and its
  members' projection records, and what the reconstruction and the flattening read at the
  addresses it holds names only addresses it holds.
* Level parameters of constructors. `check_modeled_ctors_scoped`,
  `check_inductive_shape_ctors_scoped`, `check_const_induct_ctors_scoped`:
  `KernelCheck::check_const` on an inductive type loads each of its constructors and scopes its
  type at the inductive's level count; hence `ctorLevels_of_loadChecked`, `UnitCtorLevelsAt`, `unitCtorLevelsAt_of_unitChecked`,
  `unitCtorLevelsAt_of_added`, `unitCtorLevelsAt_of_storedBelow`, `ctorLevelsDefinedAt_of_held`:
  `CtorLevelsDefinedAt` at every block a group's store holds, given it of the basis rows.
* `LoadsIn`, `CprjLoadsIn`: the calls load constants, and constructors, only at addresses of a
  set. `loadedLevelsDefined_of_loadsIn`, `cprjLevelsDefined_of_loadsIn`: at the addresses the
  store after a group holds they give the level premises. **`familyCallAnswers_of_selected`**:
  the answers of a selected family's check with the store's closure, from the run, the level
  facts of the basis rows and the two load premises.

What a selected family's check loads is not traced here: `LoadsIn` and `CprjLoadsIn` at the
store after the group are taken as premises. They hold when every address the check passes to
`Ingress::get_ci` or `Ingress::get_ci_cprj` is one of the block's or the family record's own
(`SelectedStore.block`, `.members`, `.ctors`, `.record`, `.recMembers`), an address the payload
lists (`selected_payload_held`), or an address named by a key of a term read at such an address
(`SelectedStore.reconClosed`, `.flatClosed`). -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency
open IxVM.Refinement.Binding.FamilyFlat
open IxVM.Refinement.Core (W KExpr KLevel KKey kexprEnum addrTy ixAddr Resolved)
open IxVM (F)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## A constructor's load -/

/-- **The reading of constructor `c` of member `i` of the block at `b` mentions only the
constructor's level parameters**: its type, read over the store's blobs in the block, mentions no
level parameter at or above the constructor's level count. -/
def CtorLevelsDefinedAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (b : _root_.Address)
    (i c : Nat) : Prop :=
  ∀ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive)
    (ct : Ixon.Constructor) (v : KExpr),
    recordOf E b = some cb → cb.info = .muts ms → ms[i]? = some (.indc ind) →
    ind.ctors[c]? = some ct →
    (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t b ms)).read ct.typ = .ok v →
    v.allLevelParamsDefined (List.range ct.lvls.toNat) = true

section Run

variable {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}

/-- **A constructor load of a run against the store's block**: among the calls of a bounded run
with its store, a `Ingress::get_ci_cprj` at a block, a member position and a constructor position
(both below `2^56`) whose constructor's reading mentions only its level parameters loads a `Ctor`
of the store's block record at the address: the member is an inductive, the constructor is its
constructor at the position, the payload carries the constructor's level, parameter and field
counts (the last two below `2^56`), and its type pointer represents the constructor's type
exactly, as the open loaded form at the constructor's root. -/
theorem ctorRecord_of_load (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls)
    {xblk p ci : SourceValue F} {h m : Heap F} {cs : List (Call F)} {ba : Bytes.Address}
    {i c : Nat} (hi : i < 72057594037927936) (hc : c < 72057594037927936)
    (hlv : CtorLevelsDefinedAt t E₀ (ixAddr ba) i c)
    (hb : Bytes.RepAddressRef addrTy h ba xblk)
    (ev : ObsFn W "Ingress::get_ci_cprj" [xblk, .field (i : F), .field (c : F)] h p m cs)
    (hsub : ∀ c ∈ cs, c ∈ calls) (hld : loadValue m p = .ok ci) :
    ∃ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive)
      (ct : Ixon.Constructor) (ty : KExpr) (xty xb xuns : SourceValue F),
      recordOf E₀ (ixAddr ba) = some cb ∧ cb.info = .muts ms ∧ ms[i]? = some (.indc ind) ∧
      ind.ctors[c]? = some ct ∧
      loadedAt t (fun x => E₀.blobs.get? x) cb (blockSelf t (ixAddr ba) ms) ct.lvls.toNat
        (mutsRoot ms i + 1 + ((c : Nat) : F)) ct.typ = some ty ∧
      ci = .construct "KernelTypes::KConstantInfo" "Ctor"
        [.field (ct.lvls.toNat : F), xty, xb, .field (i : F), .field (ct.cidx.toNat : F),
          .field (ct.params.toNat : F), .field (ct.fields.toNat : F), xuns] ∧
      ct.params.toNat < 72057594037927936 ∧ ct.fields.toNat < 72057594037927936 ∧
      TmOExact (keyOf t) m ty xty := by
  have hbd' := RomBound.bounded_mono hbd hsub
  have hiv : ZMod.val (i : F) = i := L1.val_cast_u56_ing hi
  have hcv : ZMod.val (c : F) = c := L1.val_cast_u56_ing hc
  obtain ⟨-, -, -, blkBytes, cb, ms, ind, ct, blobs, v, hhB, haB, hexB, -, hcb, hms, hcts, hhp,
    hld', hraw, tree, plan, built, planned, hlev⟩ := L1.get_ci_cprj_origin_spec hbd' hb ev
  rw [hiv] at hms planned hraw
  rw [hcv] at hcts
  have hvci : v = ci := Except.ok.inj (hld'.symm.trans hld)
  subst hvci
  -- the run's store holds the block the load read
  obtain ⟨value, middle, children, verified, verifiedSub⟩ :=
    Guard.get_ci_cprj_verified_subcall ev
  obtain ⟨-, bytes, c', size, hashed', address', exact', decoded', -⟩ :=
    L1.load_verified_constant_decode_bounded hb verified
  have hashedRun' : Hashed calls ⟨bytes.toArray⟩ :=
    Core.hashed_mono (fun cl member => hsub cl (verifiedSub cl member)) hashed'
  obtain ⟨lc, stored, bytesEq, -⟩ := hH ⟨bytes.toArray⟩ c' hashedRun'
    (by simpa only [ByteArray.size, List.size_toArray] using size) decoded' exact'
  have sameBytes : blkBytes = ⟨bytes.toArray⟩ :=
    hS.hashed_inj (Core.hashed_mono hsub hhB) hashedRun' (haB.trans address'.symm)
  have hrec : recordOf E₀ (ixAddr ba) = some cb := by
    have sameAddress : Address.blake3Pure ⟨bytes.toArray⟩ = ixAddr ba := address'
    have held : E₀.consts.get? (ixAddr ba) = some lc := by rw [← sameAddress]; exact stored
    apply Typing.recordOf_of_get held
    rw [bytesEq, ← sameBytes]
    exact hexB
  have hmem : ms[i]? = some (.indc ind) := by
    rw [← Array.getElem?_toList]; exact hms
  have hctm : ind.ctors[c]? = some ct := by
    rw [← Array.getElem?_toList]; exact hcts
  obtain ⟨hl, -, hnp, hnf, -, tyPtr, blkPtr, b, hbaddr, hbrep, hv, rty⟩ := hraw
  obtain ⟨count, typePtr, fields, shape, trace⟩ := hlev
  have htp : typePtr = tyPtr := by
    rw [hv] at shape
    have hargs := (Value.construct.inj shape).2.2
    simp only [List.cons.injEq] at hargs
    exact hargs.2.1.symm
  subst htp
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro x bs hmb
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hmb
    have hb' := hS.blobs bs (Core.hashed_mono hsub hhx)
    have hxa' : Address.blake3Pure bs = x := hxa
    rw [hxa'] at hb'
    exact hb'
  obtain ⟨ty, hlt, htm⟩ := loadedAt_tmOExact (t := t) (blob := fun x => E₀.blobs.get? x)
    (self := blockSelf t (ixAddr ba) ms)
    (recurAddrs := L1.blockRecurAddrs (ixAddr ba) ms.toList)
    ht hl (LoadedReads.blockSelf_key t (ixAddr ba) ms) (LoadedReads.blockSelf_ok t (ixAddr ba) ms)
    hblob rty built planned trace
    (fun v hv' => hlv cb ms ind ct v hrec hcb hmem hctm hv')
  exact ⟨cb, ms, ind, ct, ty, typePtr, blkPtr, _, hrec, hcb, hmem, hctm, hlt, hv, hnp, hnf, htm⟩

/-- **The store's field count of constructor `c` of member `i` of the block at `b`**: the count
the block's record gives the constructor. A function of the block and the two positions
(`ctorFieldsAt_unique`). -/
def ctorFieldsAt (E : Ixon.Env) (b : _root_.Address) (i c nf : Nat) : Prop :=
  ∃ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive)
    (ct : Ixon.Constructor),
    recordOf E b = some cb ∧ cb.info = .muts ms ∧ ms[i]? = some (.indc ind) ∧
    ind.ctors[c]? = some ct ∧ ct.fields.toNat = nf

/-- The store gives a constructor one field count. -/
theorem ctorFieldsAt_unique {E : Ixon.Env} {b : _root_.Address} {i c nf nf' : Nat}
    (h : ctorFieldsAt E b i c nf) (h' : ctorFieldsAt E b i c nf') : nf = nf' := by
  obtain ⟨cb, ms, ind, ct, hcb, hms, hm, hct, rfl⟩ := h
  obtain ⟨cb', ms', ind', ct', hcb', hms', hm', hct', rfl⟩ := h'
  obtain rfl : cb = cb' := Option.some.inj (hcb.symm.trans hcb')
  obtain rfl : ms = ms' := Ixon.ConstantInfo.muts.inj (hms.symm.trans hms')
  obtain rfl : ind = ind' := Ixon.MutConst.indc.inj (Option.some.inj (hm.symm.trans hm'))
  obtain rfl : ct = ct' := Option.some.inj (hct.symm.trans hct')
  rfl

/-- **The readings of the constructors the calls `calls` load mention only their level
parameters**: `CtorLevelsDefinedAt` at the block and positions (below `2^56`) of each
`Ingress::get_ci_cprj` among `calls`. -/
def CprjLevelsDefined (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (calls : List (Call F)) : Prop :=
  ∀ {xblk : SourceValue F} {h : Heap F} {ba : Bytes.Address} {i c : Nat},
    i < 72057594037927936 → c < 72057594037927936 →
    (⟨"Ingress::get_ci_cprj", [xblk, .field (i : F), .field (c : F)], h⟩ : Call F) ∈ calls →
    Bytes.RepAddressRef addrTy h ba xblk → CtorLevelsDefinedAt t E (ixAddr ba) i c

/-- Constructor readings that mention only their level parameters at the loads of some calls do
so at the loads of any part of them. -/
theorem CprjLevelsDefined.mono {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {calls cs : List (Call F)} (hlv : CprjLevelsDefined t E calls)
    (hsub : ∀ c ∈ cs, c ∈ calls) : CprjLevelsDefined t E cs :=
  fun hi hc hm hb => hlv hi hc (hsub _ hm) hb

/-- Constructor readings that mention only their level parameters at every block do so at the
loaded ones. -/
theorem cprjLevelsDefined_of_forall {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {calls : List (Call F)} (hlv : ∀ b i c, CtorLevelsDefinedAt t E b i c) :
    CprjLevelsDefined t E calls :=
  fun _ _ _ _ => hlv _ _ _

/-- The reconstruction's constructor reading of a store's block record. -/
theorem ctorAt_of_record {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {b : _root_.Address}
    {i c : Nat} {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    {ct : Ixon.Constructor} {ty : KExpr}
    (hrec : recordOf E b = some cb) (hcb : cb.info = .muts ms)
    (hmem : ms[i]? = some (.indc ind)) (hct : ind.ctors[c]? = some ct)
    (hl : loadedAt t (fun x => E.blobs.get? x) cb (blockSelf t b ms) ct.lvls.toNat
      (mutsRoot ms i + 1 + ((c : Nat) : F)) ct.typ = some ty) :
    ctorAt t E b i c = some (ty, ct.params.toNat) := by
  unfold ctorAt
  simp only [hrec, hcb, hmem, hct, hl]

/-- The flattening's constructor-type reading of a store's block record. -/
theorem ctorTypeAt_of_record {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {b : _root_.Address}
    {i c : Nat} {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    {ct : Ixon.Constructor} {ty : KExpr}
    (hrec : recordOf E b = some cb) (hcb : cb.info = .muts ms)
    (hmem : ms[i]? = some (.indc ind)) (hct : ind.ctors[c]? = some ct)
    (hl : loadedAt t (fun x => E.blobs.get? x) cb (blockSelf t b ms) ct.lvls.toNat
      (mutsRoot ms i + 1 + ((c : Nat) : F)) ct.typ = some ty) :
    ctorTypeAt t E b i c = some ty := by
  unfold ctorTypeAt
  simp only [hrec, hcb, hmem, hct, hl]

/-- **`CtorAnswers` of a run**: among the calls of a bounded run with its store, where the
readings of the constructors the run loads mention only their level parameters, a constructor
load returns the store's constructor at the block and positions, its type represented exactly as
the open loaded form. -/
theorem ctorAnswers_of_run (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls) {root : List (Call F)} (hroot : ∀ c ∈ root, c ∈ calls)
    (hlv : CprjLevelsDefined t E₀ root) :
    CtorAnswers root (keyOf t) (ReconView.ofStore t E₀) := by
  intro xblk p ci h m cs ba i c hi hc hb ev hself hsub hld xnl xty xb xind xcidx xnp xnf xuns hci
  obtain ⟨cb, ms, ind, ct, ty, xty', xb', xuns', hrec, hcb, hmem, hct, hl, hci', hnp, hnf, htm⟩ :=
    ctorRecord_of_load ht hS hH hbd hi hc (hlv hi hc hself hb) hb ev
      (fun c hc => hroot c (hsub c hc)) hld
  rw [hci'] at hci
  have hargs := (Value.construct.inj hci).2.2
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨-, e2, -, -, -, e6, -, -⟩ := hargs
  exact ⟨ty, ct.params.toNat, ctorAt_of_record hrec hcb hmem hct hl, hnp, e2 ▸ htm, e6.symm⟩

/-- **`CprjAnswers` of a run**, at the store's field counts (`ctorFieldsAt`): among the calls of
a bounded run with its store, where the readings of the constructors the run loads mention only
their level parameters, a constructor load returns the store's constructor at the block and
positions, with its parameter and field counts, its type represented exactly as the open loaded
form. A constructor load returns no other kind. -/
theorem cprjAnswers_of_run (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls) {root : List (Call F)} (hroot : ∀ c ∈ root, c ∈ calls)
    (hlv : CprjLevelsDefined t E₀ root) :
    CprjAnswers root (keyOf t) (ReconView.ofStore t E₀) (ctorFieldsAt E₀) := by
  intro xblk p ci h m cs ba i c hb hi hc ev hself hsub hld
  obtain ⟨cb, ms, ind, ct, ty, xty', xb', xuns', hrec, hcb, hmem, hct, hl, hci', hnp, hnf, htm⟩ :=
    ctorRecord_of_load ht hS hH hbd hi hc (hlv hi hc hself hb) hb ev
      (fun c hc => hroot c (hsub c hc)) hld
  constructor
  · intro xnl xty xb xi xci xnp xnf xu hci
    rw [hci'] at hci
    have hargs := (Value.construct.inj hci).2.2
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨-, e2, -, -, -, e6, e7, -⟩ := hargs
    exact ⟨ty, ct.params.toNat, ct.fields.toNat, ctorAt_of_record hrec hcb hmem hct hl, hnp, hnf,
      e2 ▸ htm, e6.symm, e7.symm, cb, ms, ind, ct, hrec, hcb, hmem, hct, rfl⟩
  · intro hne
    exact absurd hci' (hne _ rfl)

/-- **`FlatCtorAnswersIn` of a run**: among the calls of a bounded run with its store, at the
blocks of `S` the readings of whose constructors mention only their level parameters, a
constructor load returns the constructor type the flattening reads of the store, represented
exactly. -/
theorem flatCtorAnswersIn_of_run (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls) {root : List (Call F)} (hroot : ∀ c ∈ root, c ∈ calls)
    {S : _root_.Address → Prop}
    (hlv : ∀ b, S b → ∀ i c, CtorLevelsDefinedAt t E₀ b i c) :
    FlatCtorAnswersIn root S (keyOf t) (FlatView.ofStore t E₀) := by
  intro xblk p ci h m cs ba i c hb ev hsub hSb hi hc hld xnl xty xb xind xcidx xnp xnf xuns hci
  obtain ⟨cb, ms, ind, ct, ty, xty', xb', xuns', hrec, hcb, hmem, hct, hl, hci', hnp, hnf, htm⟩ :=
    ctorRecord_of_load ht hS hH hbd hi hc (hlv _ hSb i c) hb ev
      (fun c hc => hroot c (hsub c hc)) hld
  rw [hci'] at hci
  have hargs := (Value.construct.inj hci).2.2
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨-, e2, -, -, -, -, -, -⟩ := hargs
  exact ⟨ty, ctorTypeAt_of_record hrec hcb hmem hct hl, e2 ▸ htm⟩

/-! ## A constructor's address -/

/-- Every key of a role table's keying resolves. -/
theorem resolved_keyOf (t : Ix.Kernel.RoleTable) (a : _root_.Address) : Resolved (keyOf t a) := by
  refine ⟨fun he => ?_⟩
  rcases keyOf_cases t a with ⟨h, -⟩ | ⟨r, -, h⟩
  · rw [h] at he
    cases he
  · rw [h] at he
    cases he

/-- **`CtorAddrAnswers` of a run**: among the calls of a bounded run, the address
`KernelCheck::projection_addr_ctor` computes at positions below `2^56` is the constructor's
constant address, keyed by the table. -/
theorem ctorAddrAnswers_of_run (hbd : Bounded calls) {root : List (Call F)}
    (hroot : ∀ c ∈ root, c ∈ calls) (E : Ixon.Env) :
    CtorAddrAnswers root (keyOf t) (ReconView.ofStore t E) := by
  intro xblk r h h' cs ba i c hi hc hb ev hself hsub
  obtain ⟨ca, hca, haddr⟩ := Typing.FamilyAlias.projection_addr_ctor_bounded ev
    (RomBound.bounded_mono hbd (fun c hc => hroot c (hsub c hc))) hb
  rw [L1.val_cast_u56_ing hi, L1.val_cast_u56_ing hc] at haddr
  refine ⟨ca, hca, ?_, resolved_keyOf t _⟩
  rw [haddr]
  rfl

/-! ## A block's member addresses -/

/-- **`KernelCheck::flat_originals_walk`** over the members of a block from position `k` lists
the constant addresses of its inductive members (`indcAddrs`), each entry read for its address
alone: no store, level count or offset is asked. -/
theorem flat_originals_walk_addrs {bP : Bytes.Address} {all : List Ixon.MutConst}
    (hsz : all.length < 8589934592) {x_all x_blk xoff : SourceValue F} :
    ∀ (cur : List Ixon.MutConst) (k : Nat) {x_cur r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      (∀ j m, cur[j]? = some m → all[k + j]? = some m) →
      RepList L1.mutConstListEnum L1.RepMutConst h all x_all →
      RepList L1.mutConstListEnum L1.RepMutConst h cur x_cur →
      Bytes.RepAddressRef addrTy h bP x_blk →
      ObsFn W "KernelCheck::flat_originals_walk" [x_all, x_cur, x_blk, xoff, .field (k : F)] h r
        h' cs →
      Heap.Extends h h' ∧
      RepList flatListEnum MemberAddrRep h' (indcAddrs (ixAddr bP) k cur) r := by
  intro cur
  induction cur with
  | nil =>
    intro k x_cur r h h' cs _ _ hcur _ ev
    match Obs.«KernelCheck::flat_originals_walk».obs ev with
    | .Nil (he24 := hr) (hm23 := hh) .. =>
      rw [hr, hh]
      exact ⟨Heap.Extends.snoc _ _, Lib.rep_store_nil h⟩
    | .Cons_Indc (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hcur ld
      cases he
  | cons m rest ih =>
    intro k x_cur r h h' cs hsuf hall hcur hb ev
    have hm0 : all[k]? = some m := by simpa using hsuf 0 m rfl
    have hklt : k < all.length := (List.getElem?_eq_some_iff.mp hm0).1
    have hsuf' : ∀ j m', rest[j]? = some m' → all[k + 1 + j]? = some m' := fun j m' hj => by
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
      have hrec := ih (k + 1) hsuf' hall hrest hb evR
      cases m with
      | indc ind =>
        obtain ⟨iv, hiv, -⟩ := hm
        exact absurd hiv (hne [iv] rfl)
      | defn d => simpa only [indcAddrs] using hrec
      | recr rc => simpa only [indcAddrs] using hrec
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
        obtain ⟨ext1, -, -, mc, a, hget, ha_rep, ha_eq, -⟩ :=
          L1.projection_addr_hashed_spec (Route.membersRep_of_repMutConstList hall) hb e1
        rw [hkval, hm0] at hget
        have hmc : mc = .indc ind := (Option.some.inj hget).symm
        subst hmc
        rw [hkval] at ha_eq
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
        obtain ⟨ext5, hrep⟩ := ih (k + 1) hsuf'
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
        refine ⟨extR.trans (ext5.trans (Heap.Extends.snoc _ _)), ?_⟩
        simp only [indcAddrs]
        exact Lib.rep_store_cons memberAddrRep_heapMono₂ hentry hrep

/-- **`KernelCheck::build_flat_originals`** on a block record of the run's store lists the
constant addresses of the block's inductive members (`membersAt`), at any offset. -/
theorem build_flat_originals_addrs (hS : LoadedReads.RunStore calls E₀)
    {bP : Bytes.Address} {cP : Ixon.Constant} {mP : Array Ixon.MutConst}
    (hcP : recordOf E₀ (ixAddr bP) = some cP) (hmP : cP.info = .muts mP)
    {x_blk xoff r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hb : Bytes.RepAddressRef addrTy h bP x_blk)
    (ev : ObsFn W "KernelCheck::build_flat_originals" [x_blk, xoff] h r h' cs)
    (hsub : ∀ c ∈ cs, c ∈ calls) :
    Heap.Extends h h' ∧
    RepList flatListEnum MemberAddrRep h' (indcAddrs (ixAddr bP) 0 mP.toList) r := by
  match Obs.«KernelCheck::build_flat_originals».obs ev with
  | .Muts (cs12 := csL) (cs92 := csW) (ev14 := evL) (ev94 := evW) (hc134 := hc) .. =>
    obtain ⟨msPtr, hxm, hlist, hlt⟩ := Decl.load_block_info hS hb evL
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hcP hmP
    have hxe := (List.cons.inj (Value.construct.inj hxm).2.2).1
    subst hxe
    have extL := evL.heap_extends
    obtain ⟨ext, res⟩ := flat_originals_walk_addrs (bP := bP) (all := mP.toList)
      (by rw [Array.length_toList]; exact hlt) mP.toList 0
      (fun j m hj => by rw [Nat.zero_add]; exact hj) hlist hlist
      (Bytes.repAddressRef_heapMono₂ addrTy extL hb) (by simpa using evW)
    exact ⟨extL.trans ext, res⟩
  | .other_Induct (cs12 := csL) (ev14 := evL) (hne135 := hne) (hc332 := hc) .. =>
    obtain ⟨msPtr, hxm, -, -⟩ := Decl.load_block_info hS hb evL
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hcP hmP
    exact absurd hxm (hne [msPtr] rfl)
  | .other_other (cs12 := csL) (ev14 := evL) (hne135 := hne) (hc345 := hc) .. =>
    obtain ⟨msPtr, hxm, -, -⟩ := Decl.load_block_info hS hb evL
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hcP hmP
    exact absurd hxm (hne [msPtr] rfl)

/-- **`FlatMembersAnswersIn` of a run**: among the calls of a run with its store,
`KernelCheck::build_flat_originals` at the block of an inductive type the store reads lists the
member addresses the flattening reads of the block. -/
theorem flatMembersAnswersIn_of_run (hS : LoadedReads.RunStore calls E₀)
    {root : List (Call F)} (hroot : ∀ c ∈ root, c ∈ calls) :
    FlatMembersAnswersIn root (FlatView.ofStore t E₀) := by
  intro xblk r h m cs ba a d hb ev hsub hci hba
  obtain ⟨cb, ms, hcb, hms⟩ := FamilyFlatBuild.indInfoAt_block (E := E₀) (a := a) (i := d) hci
  rw [← hba] at hcb
  obtain ⟨-, hrep⟩ := build_flat_originals_addrs hS hcb hms hb ev
    (fun c hc => hroot c (hsub c hc))
  refine ⟨indcAddrs (ixAddr ba) 0 ms.toList, ?_, hrep⟩
  show membersAt E₀ d.blk = _
  unfold membersAt
  rw [← hba]
  simp only [hcb, hms]

/-! ## The loads of a part of a run -/

/-- **`DefnAnswers` of a part of a run**: among calls `root` of a bounded run with its store, the
readings at whose loaded addresses mention only their level parameters
(`LoadedLevelsDefined` of `root` alone). -/
theorem defnAnswers_of_sub (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls) {root : List (Call F)} (hroot : ∀ c ∈ root, c ∈ calls)
    (hlv : LoadedLevelsDefined t E₀ root) :
    DefnAnswers root (keyOf t) (ReconView.ofStore t E₀) := by
  intro xa p ci h m cs a ha ev hself hsub hld
  obtain ⟨X, hX, hsome, hnone⟩ := defnAt_of_load ht hS hH hbd (hlv hself ha) ha ev
    (fun c hc => hroot c (hsub c hc)) hld
  exact defn_clause_of_defnAt hwf hX hsome hnone

/-- **`IndAnswers` of a part of a run**: among calls `root` of a bounded run with its store, the
readings at whose loaded addresses mention only their level parameters. -/
theorem indAnswers_of_sub (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls) {root : List (Call F)} (hroot : ∀ c ∈ root, c ∈ calls)
    (hlv : LoadedLevelsDefined t E₀ root) :
    IndAnswers root (keyOf t) (ReconView.ofStore t E₀) := by
  intro xa p ci h m cs a ha ev hself hsub hld
  exact indDataAt_of_load ht hS hH hbd (hlv hself ha) ha ev (fun c hc => hroot c (hsub c hc)) hld

/-- `CtorOfAnswers` of some calls is `CtorOfAnswers` of any part of them. -/
theorem CtorOfAnswers.mono {V : ReconView} {root : List (Call F)}
    (h : CtorOfAnswers calls V) (hroot : ∀ c ∈ root, c ∈ calls) : CtorOfAnswers root V :=
  fun ha ev hsub hld => h ha ev (fun c hc => hroot c (hsub c hc)) hld

/-- `ModeledAnswers` of some calls is `ModeledAnswers` of any part of them. -/
theorem ModeledAnswers.mono {V : ReconView} {root : List (Call F)}
    (h : ModeledAnswers calls V) (hroot : ∀ c ∈ root, c ∈ calls) : ModeledAnswers root V :=
  fun hb ev hsub => h hb ev (fun c hc => hroot c (hsub c hc))

/-- **`GuardDefnAnswers` of a part of a run**, at the store's definition lookup. -/
theorem guardDefnAnswers_of_sub (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls) {root : List (Call F)} (hroot : ∀ c ∈ root, c ∈ calls)
    (hlv : LoadedLevelsDefined t E₀ root) :
    GuardDefnAnswers (keyOf t) (defnValAt t E₀) root := by
  intro xa p xnl xty xval xsf xh h m cs a ha ev hself hsub hld
  obtain ⟨X, hX, hsome, hnone⟩ := defnAt_of_load ht hS hH hbd (hlv hself ha) ha ev
    (fun c hc => hroot c (hsub c hc)) hld
  cases X with
  | none => exact absurd rfl (hnone rfl _)
  | some nv =>
    obtain ⟨n, v⟩ := nv
    obtain ⟨xty', xval', xsf', xh', hci, hn, htm⟩ := hsome n v rfl
    have hargs := (Value.construct.inj hci).2.2
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨e1, -, e3, -, -⟩ := hargs
    exact ⟨n, v, defnValAt_of_defnAt hX, e1, hn, e3 ▸ htm⟩

/-! ## All the answers of one call list -/

/-- **Every store answer the reconstruction and the flattening read, for the calls `cs`**, at the
table's keying and the readings of the store `E`: the key-address maps, the definition, inductive,
constructor-owner and modeled-route answers of `Ingress::get_ci` and the dispatch, the constructor
answers of `Ingress::get_ci_cprj` (in each of the three forms the reconstruction and the
flattening ask, the flattening's at the blocks of `S`), the constructor addresses, the member
addresses of `KernelCheck::build_flat_originals`, the guard's definition and inductive lookups,
and the keying's facts (the view's key is the keying, every key resolves, the keying is
injective). -/
structure FamilyCallAnswers (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (cs : List (Call F))
    (S : _root_.Address → Prop) : Prop where
  addrOf : AddrOf (keyOf t) (ReconView.ofStore t E)
  defn : DefnAnswers cs (keyOf t) (ReconView.ofStore t E)
  ind : IndAnswers cs (keyOf t) (ReconView.ofStore t E)
  ctorOf : CtorOfAnswers cs (ReconView.ofStore t E)
  modeled : ModeledAnswers cs (ReconView.ofStore t E)
  ctor : CtorAnswers cs (keyOf t) (ReconView.ofStore t E)
  ctorAddr : CtorAddrAnswers cs (keyOf t) (ReconView.ofStore t E)
  cprj : CprjAnswers cs (keyOf t) (ReconView.ofStore t E) (ctorFieldsAt E)
  flatAddrOf : FlatAddrOf (keyOf t) (FlatView.ofStore t E)
  flatInd : FlatIndAnswersIn cs (FlatView.ofStore t E)
  flatCtor : FlatCtorAnswersIn cs S (keyOf t) (FlatView.ofStore t E)
  flatMembers : FlatMembersAnswersIn cs (FlatView.ofStore t E)
  guardDefn : GuardDefnAnswers (keyOf t) (defnValAt t E) cs
  guardInd : GuardIndAnswers (keyOf t) (indTypeAt t E) cs
  key : ∀ a, (ReconView.ofStore t E).key a = keyOf t a
  resolved : ∀ a, Resolved (keyOf t a)
  inj : Function.Injective (keyOf t)
  fields : ∀ b i c nf nf', ctorFieldsAt E b i c nf → ctorFieldsAt E b i c nf' → nf = nf'

/-- **The store answers of a part of a run**: for calls `cs` of a bounded run with its store that
hashes no collision with the store, where the readings at the addresses `cs` loads
(`LoadedLevelsDefined`), of the constructors `cs` loads (`CprjLevelsDefined`) and of the
constructors of the blocks of `S` mention only their level parameters. The level premises are
asked of `cs` alone. -/
theorem familyCallAnswers_of_sub (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls) (hnc : ¬ View.HashedCollision { env := E₀ } [] calls)
    {cs : List (Call F)} (hsub : ∀ c ∈ cs, c ∈ calls)
    (hlv : LoadedLevelsDefined t E₀ cs) (hclv : CprjLevelsDefined t E₀ cs)
    {S : _root_.Address → Prop} (hslv : ∀ b, S b → ∀ i c, CtorLevelsDefinedAt t E₀ b i c) :
    FamilyCallAnswers t E₀ cs S := by
  have hwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  have hI : IndAnswers cs (keyOf t) (ReconView.ofStore t E₀) :=
    indAnswers_of_sub ht hS hH hbd hsub hlv
  exact
    { addrOf := addrOf_ofStore hwf E₀
      defn := defnAnswers_of_sub ht hwf hS hH hbd hsub hlv
      ind := hI
      ctorOf := CtorOfAnswers.mono (ctorOfAnswers_of_run hS hH hbd) hsub
      modeled := ModeledAnswers.mono (modeledAnswers_of_run hH hbd hnc) hsub
      ctor := ctorAnswers_of_run ht hS hH hbd hsub hclv
      ctorAddr := ctorAddrAnswers_of_run hbd hsub E₀
      cprj := cprjAnswers_of_run ht hS hH hbd hsub hclv
      flatAddrOf := flatAddrOf_ofStore hwf E₀
      flatInd := flatIndAnswersIn_ofStore hI
      flatCtor := flatCtorAnswersIn_of_run ht hS hH hbd hsub hslv
      flatMembers := flatMembersAnswersIn_of_run hS hsub
      guardDefn := guardDefnAnswers_of_sub ht hS hH hbd hsub hlv
      guardInd := guardIndAnswers_of_indAnswers hI
      key := fun _ => rfl
      resolved := resolved_keyOf t
      inj := fun _ _ h => IxVM.Refinement.Core.keyOf_inj hwf h
      fields := fun _ _ _ _ _ h h' => ctorFieldsAt_unique h h' }

/-- **The store answers of one family call**: `familyCallAnswers_of_sub` at the calls of an
observed `KernelModeled::check_family`. -/
theorem familyCallAnswers (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls) (hnc : ¬ View.HashedCollision { env := E₀ } [] calls)
    {bAddr B rb : _root_.Address} {lim : Option Nat} {cs : List (Call F)}
    (hfc : Typing.FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs)
    (hlv : LoadedLevelsDefined t E₀ cs) (hclv : CprjLevelsDefined t E₀ cs)
    {S : _root_.Address → Prop} (hslv : ∀ b, S b → ∀ i c, CtorLevelsDefinedAt t E₀ b i c) :
    FamilyCallAnswers t E₀ cs S := by
  obtain ⟨h, h', rc, xb, xrb, r, -, -, -, -, -, hsub⟩ := hfc
  exact familyCallAnswers_of_sub ht hS hH hbd hnc hsub hlv hclv hslv

end Run

end IxVM.Refinement.Binding.FamilyRecon

namespace IxVM.Refinement.Binding.FamilyLoadAnswers

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)
open IxVM.Refinement.Typing
open IxVM.Refinement (View)
open IxVM.Refinement.StoreInhabit (basisStore)
open IxVM.Refinement.Binding.FamilyFlat (Held FlatView)
open IxVM.Refinement.Binding.FamilyRecon (ReconView LoadedLevelsDefined LevelsDefinedAt
  CtorLevelsDefinedAt CprjLevelsDefined FamilyCallAnswers familyCallAnswers)
open IxVM.Refinement.Binding.FamilyCallPremises

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The store after the group of a selected family -/

section Selected

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env}

/-- **An address the family check of a selected block names is reached through the group's
payload**, the block's record taken from the family check (`FamBlockRecord`): the selected block
is new in its group's admission, which reaches a block record by its walk or through its
payload. -/
theorem selected_payload_reach (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hP : PayloadFacts t E₀ (runPayload calls bAddr t))
    {g : Nat} (hg6 : 6 ≤ g)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) {B rb a : _root_.Address}
    (hfam : runFamOf calls bAddr t E₀ g B = some rb)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} (hB : FamBlockRecord E₀ B cb ms)
    (hpay : runPayload calls bAddr t g B a) :
    PayReach t E₀ (runPayload calls bAddr t) g a := by
  obtain ⟨hnew, -, -⟩ := runFamOf_spec hfam
  obtain ⟨-, -, -, hadd, -⟩ := new_groupStore hb hg6 hnew
  rcases groupAdds_cases hC hax hw hadd with ⟨hra, -⟩ | ⟨-, -, -, -, p, hp, hproj, -⟩ |
      ⟨-, -, -, -, c₂, ax, hc₂, hinfo, -⟩ | hpa
  · exact PayReach.payload hra hpay
  · have e : p = cb := Option.some.inj (hp.symm.trans hB.record)
    rw [e] at hproj
    exact (proj_not_block hproj ⟨ms, hB.muts⟩).elim
  · have e : c₂ = cb := Option.some.inj (hc₂.symm.trans hB.record)
    rw [e, hB.muts] at hinfo
    cases hinfo
  · rcases payAdds_cases hP hpa with ⟨hrB, -⟩ | ⟨-, -, -, -, -, p, hp, hproj, -⟩
    · exact PayReach.payloadOf hrB hpay
    · have e : p = cb := Option.some.inj (hp.symm.trans hB.record)
      rw [e] at hproj
      exact (proj_not_block hproj ⟨ms, hB.muts⟩).elim

/-- **An address the family check of a selected block names is held after the group**
(`selected_payload_reach`). -/
theorem selected_payload_held (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hP : PayloadFacts t E₀ (runPayload calls bAddr t))
    {g : Nat} (hg6 : 6 ≤ g)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) {B rb a : _root_.Address}
    (hfam : runFamOf calls bAddr t E₀ g B = some rb)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} (hB : FamBlockRecord E₀ B cb ms)
    (hpay : runPayload calls bAddr t g B a) :
    Held (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a := by
  have hreach := selected_payload_reach hC hb hax hP hg6 hw hfam hB hpay
  obtain ⟨c, hc⟩ := hP.record g a hreach
  rw [Held, (groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mpr
    ⟨storedBelow_of_adds hg6 (GroupAdds.payReach hreach), hc⟩]
  rfl

/-- **What the store after the group of a selected family holds, and is closed under**: a
sub-store of the run's, closed under used references, owners, members and constructors
(`UsedClosed`), that holds the block, its members' and constructors' projection records, the
family record and its members' projection records; and what the reconstruction and the flattening
read of the run's store at the addresses it holds names only addresses it holds. -/
structure SelectedStore (t : Ix.Kernel.RoleTable) (E₀ R : Ixon.Env) (B rb : _root_.Address) :
    Prop where
  sub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c
  usedClosed : UsedClosed R
  block : Held R B
  record : Held R rb
  members : ∀ cb ms i m, recordOf E₀ B = some cb → cb.info = .muts ms → ms[i]? = some m →
    Held R (memberAddr B i m)
  ctors : ∀ cb ms i ind j, recordOf E₀ B = some cb → cb.info = .muts ms →
    ms[i]? = some (.indc ind) → j < ind.ctors.size → Held R (ctorAddr B i j)
  recMembers : ∀ crb rs k m, recordOf E₀ rb = some crb → crb.info = .muts rs → rs[k]? = some m →
    Held R (memberAddr rb k m)
  reconClosed : (ReconView.ofStore t E₀).ClosedOn (Held R)
  flatClosed : (FlatView.ofStore t E₀).ClosedOn (Held R)

/-- **The store after the group of a selected family** (`SelectedStore`), for a bounded run with a
collision-free store that validates every role of the 77 groups. No family clause of the run is
asked: the family record is reached through the payload of the block, a block record by the
family check's own facts. -/
theorem selectedStore_of_run (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀) (hpin : PreludePinned t)
    (hcheck : t.check = .ok ()) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    {g : Nat} (hg6 : 6 ≤ g) (hg : g < 77) {B rb : _root_.Address}
    (hf : runFamOf calls bAddr t E₀ g B = some rb) :
    SelectedStore t E₀ (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B rb := by
  have hwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [hcheck]; rfl
  have hvalAll : ∀ g, ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r := by
    intro g r hr
    by_cases hg : g < 77
    · exact hval g hg r hr
    · rw [roleGroup_eq_nil (by rw [groups_length]; omega)] at hr
      cases hr
  have hax := axiomRoles_of_run hC hval
  have hP := payloadFacts_of_validated hC hbd hb hpin hcheck hstep hval
  have hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs :=
    fun k => groupWalked_exists hC.hashedStored (hvalAll k)
  have hcl := groupStore_usedClosed_all hC hb (basisRolesStored_of_pinned hpin) hax hP hws
    (g + 1) (Nat.le_succ_of_le hg6)
  have hsub : ∀ y c, recordOf (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) y = some c →
      recordOf E₀ y = some c :=
    fun y c h => ((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp h).2
  obtain ⟨hnew, -, -⟩ := runFamOf_spec hf
  obtain ⟨cB, hcB, hcBR, -, -⟩ := new_groupStore hb hg6 hnew
  obtain ⟨cb, ms, hB⟩ := famBlockRecord_of_selected hC hbd hb hpin hcheck hstep hval hg6 hg hf
  obtain ⟨recs, hw⟩ := hws g
  have hreach := selected_payload_reach hC hb hax hP hg6 hw hf hB (runFamOf_payload hf)
  obtain ⟨crb, hcrb⟩ := hP.record g rb hreach
  have hrbR : recordOf (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) rb = some crb :=
    (groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mpr
      ⟨storedBelow_of_adds hg6 (GroupAdds.payReach hreach), hcrb⟩
  refine
    { sub := hsub
      usedClosed := hcl
      block := hnew.1
      record := by rw [Held, hrbR]; rfl
      members := fun cb' ms' i m hcb' hms' hm => ?_
      ctors := fun cb' ms' i ind j hcb' hms' hm hj => ?_
      recMembers := fun crb' rs k m hcrb' hrs hm => ?_
      reconClosed := FamilyRecon.reconOfStore_closedOn_sub hcheck hwf hsub hcl
      flatClosed := FamilyFlat.ofStore_closedOn_sub hcheck hwf hsub hcl }
  · have e : cb' = cB := Option.some.inj (hcb'.symm.trans hcB)
    subst e
    rw [Held, (hcl.2 B cb' ms' hcBR hms' i m hm).1]
    rfl
  · have e : cb' = cB := Option.some.inj (hcb'.symm.trans hcB)
    subst e
    rw [Held, (hcl.2 B cb' ms' hcBR hms' i _ hm).2 ind rfl j hj]
    rfl
  · have e : crb' = crb := Option.some.inj (hcrb'.symm.trans hcrb)
    subst e
    rw [Held, (hcl.2 rb crb' rs hrbR hrs k m hm).1]
    rfl

/-! ## The loads of a family call, at held addresses -/

/-- **Every `Ingress::get_ci` among the calls `cs` at an address the store `E` has a record at is
at an address of `S`.** For the calls of a family check and the addresses a group's store holds,
this is a fact of which loads the check makes. -/
def LoadsIn (E : Ixon.Env) (cs : List (Call F)) (S : _root_.Address → Prop) : Prop :=
  ∀ {xa : SourceValue F} {h : Heap F} {a : Bytes.Address},
    (⟨"Ingress::get_ci", [xa], h⟩ : Call F) ∈ cs → Bytes.RepAddressRef addrTy h a xa →
    (recordOf E (ixAddr a)).isSome = true → S (ixAddr a)

/-- Loads at addresses of `S` are loads at addresses of any larger set, among any part of the
calls. -/
theorem LoadsIn.mono {E : Ixon.Env} {cs cs' : List (Call F)} {S S' : _root_.Address → Prop}
    (h : LoadsIn E cs S) (hsub : ∀ c ∈ cs', c ∈ cs) (hS : ∀ a, S a → S' a) : LoadsIn E cs' S' :=
  fun hm ha hr => hS _ (h (hsub _ hm) ha hr)

/-- **The readings at the addresses the calls `cs` load mention only their constant's level
parameters** (`FamilyRecon.LoadedLevelsDefined`), when `cs` loads only addresses the store after
group `g` holds (`LoadsIn`), given the same of the basis rows (`hbasis`). -/
theorem loadedLevelsDefined_of_loadsIn (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀) (hpin : PreludePinned t)
    (hcheck : t.check = .ok ()) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    (hbasis : ∀ A, (basisStore.consts.get? A).isSome = true → UnitLevelsAt t E₀ A)
    {g : Nat} (hg6 : 6 ≤ g) (hg : g < 77) {cs : List (Call F)}
    (hin : LoadsIn E₀ cs (Held (groupStore t E₀ (runPayload calls bAddr t) (g + 1)))) :
    LoadedLevelsDefined t E₀ cs :=
  loadedLevelsDefined_of_held hC hbd hb hpin hcheck hstep hval hbasis
    (fun hm ha hr => ⟨g + 1, Nat.le_succ_of_le hg6, hg, hin hm ha hr⟩)

end Selected

/-! ## Level parameters of a checked inductive's constructors -/

/-- **An observed, scope-checked load of constructor `c`** of the member `xidx` of the block
`xblk`, among the calls `calls` and from the heap `h` on: an `Ingress::get_ci_cprj` that returns a
`Ctor` whose level count is `xnl`, and a `KernelCheck::validate_expr_well_scoped` of its type at
`xnl`. -/
def CtorScopedAt (calls : List (Call F)) (xblk xidx xnl : SourceValue F) (h : Heap F)
    (c : Nat) : Prop :=
  ∃ (h1 m m2 m3 : Heap F) (p xcty xb xi xc xnp xnf xu v : SourceValue F)
    (cs csv : List (Call F)),
    Heap.Extends h h1 ∧
    ObsFn Obs.W "Ingress::get_ci_cprj" [xblk, xidx, .field (c : F)] h1 p m cs ∧
    (∀ x ∈ cs, x ∈ calls) ∧
    loadValue m p = .ok (.construct "KernelTypes::KConstantInfo" "Ctor"
      [xnl, xcty, xb, xi, xc, xnp, xnf, xu]) ∧
    Heap.Extends m m2 ∧
    ObsFn Obs.W "KernelCheck::validate_expr_well_scoped" [xcty, .field 0, xnl] m2 v m3 csv ∧
    (⟨"KernelCheck::validate_expr_well_scoped", [xcty, .field 0, xnl], m2⟩ : Call F) ∈ calls

theorem CtorScopedAt.mono {calls calls' : List (Call F)} {xblk xidx xnl : SourceValue F}
    {h h' : Heap F} {c : Nat} (hs : CtorScopedAt calls xblk xidx xnl h c)
    (hsub : ∀ x ∈ calls, x ∈ calls') (hext : Heap.Extends h' h) :
    CtorScopedAt calls' xblk xidx xnl h' c := by
  obtain ⟨h1, m, m2, m3, p, xcty, xb, xi, xc, xnp, xnf, xu, v, cs, csv, e0, ev, hcs, ld, e1, evs,
    hmem⟩ := hs
  exact ⟨h1, m, m2, m3, p, xcty, xb, xi, xc, xnp, xnf, xu, v, cs, csv, hext.trans e0, ev,
    fun x hx => hsub x (hcs x hx), ld, e1, evs, hsub _ hmem⟩

private theorem natCast_sub_ne {n k : Nat} (hn : n < 72057594037927936) (hk : k ≤ n)
    {v : SourceValue F}
    (op : evalBinOp .sub (.field (n : F) : SourceValue F) (.field (k : F)) = .ok v) :
    v = .field 0 → n = k := by
  intro hv
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  have e := SubstAux.sub_ok op
  rw [hv] at e
  have hnj : ((n : F)) = (k : F) := sub_eq_zero.mp (Value.field.inj e).symm
  have := congrArg ZMod.val hnj
  rw [SubstAux.val_natCast (by omega), SubstAux.val_natCast (by omega)] at this
  exact this

/-- **`KernelCheck::check_modeled_ctors` loads and scope-checks every remaining constructor.** -/
theorem check_modeled_ctors_scoped {nctors : Nat} (hnc : nctors < 72057594037927936)
    {rc xnp xni xnl xblk xidx xuns : SourceValue F} :
    ∀ (n cidx : Nat), nctors - cidx = n → cidx ≤ nctors →
      ∀ {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn Obs.W "KernelCheck::check_modeled_ctors"
        [rc, xnp, xni, .field (nctors : F), xnl, xblk, xidx, xuns, .field (cidx : F)] h r h' cs →
      ∀ c, cidx ≤ c → c < nctors → CtorScopedAt cs xblk xidx xnl h c
  | 0, cidx, hn, hle, r, h, h', cs, ev => fun c h1 h2 => by omega
  | n + 1, cidx, hn, hle, r, h, h', cs, ev => by
    match Obs.«KernelCheck::check_modeled_ctors».obs ev with
    | .n0 (op17 := op) .. =>
      have := natCast_sub_ne hnc hle op rfl
      omega
    | .other (m34 := m34) (p41 := p41) (cs47 := cs47) (x_cty := xcty) (m144 := m144)
        (m319 := m319) (cs329 := cs329) (m387 := m387) (m356 := m356) (m400 := m400)
        (m430 := m430) (m500 := m500) (m551 := m551)
        (ev49 := e1) (ld43 := ld) (ev154 := e2) (heq261 := hnl) (ev331 := e3) (hm395 := hm)
        (ev368 := e4) (ev412 := e5) (ev442 := e6) (ev512 := e7) (ev561 := e8) (op669 := op)
        (ev590 := evR) (hc671 := hc) .. =>
      rw [hnl] at ld
      obtain rfl := FamilyRecon.binop_add_one_nat op
      subst hc
      intro c hc1 hc2
      rcases Nat.eq_or_lt_of_le hc1 with rfl | hlt
      · exact ⟨h, m34, m144, m319, p41, xcty, _, _, _, _, _, _, _, cs47, cs329,
          Heap.Extends.refl _, e1, fun x hx => by simp [hx], ld, e2.heap_extends, e3, by simp⟩
      · have ih := check_modeled_ctors_scoped hnc n (cidx + 1) (by omega) (by omega) evR c hlt hc2
        have e45 : Heap.Extends m319 m387 := by rw [hm]; exact Heap.Extends.snoc _ _
        exact ih.mono (fun x hx => by simp [hx])
          (e1.heap_extends.trans (e2.heap_extends.trans (e3.heap_extends.trans (e45.trans
            (e4.heap_extends.trans (e5.heap_extends.trans (e6.heap_extends.trans
              (e7.heap_extends.trans e8.heap_extends))))))))

/-- **`KernelCheck::check_inductive_shape_ctors` loads and scope-checks every remaining
constructor.** -/
theorem check_inductive_shape_ctors_scoped {nctors : Nat} (hnc : nctors < 72057594037927936)
    {rc xity xnp xni xnl xblk xidx xlvl xuns : SourceValue F} :
    ∀ (n cidx : Nat), nctors - cidx = n → cidx ≤ nctors →
      ∀ {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn Obs.W "KernelCheck::check_inductive_shape_ctors"
        [rc, xity, xnp, xni, .field (nctors : F), xnl, xblk, xidx, xlvl, xuns,
          .field (cidx : F)] h r h' cs →
      ∀ c, cidx ≤ c → c < nctors → CtorScopedAt cs xblk xidx xnl h c
  | 0, cidx, hn, hle, r, h, h', cs, ev => fun c h1 h2 => by omega
  | n + 1, cidx, hn, hle, r, h, h', cs, ev => by
    match Obs.«KernelCheck::check_inductive_shape_ctors».obs ev with
    | .n0 (op17 := op) .. =>
      have := natCast_sub_ne hnc hle op rfl
      omega
    | .other (m34 := m34) (p41 := p41) (cs47 := cs47) (x_cty := xcty) (m144 := m144)
        (m319 := m319) (cs329 := cs329) (m387 := m387) (m592 := m592) (m716 := m716)
        (ev49 := e1) (ld43 := ld) (ev154 := e2) (heq261 := hnl) (ev331 := e3) (hm395 := hm)
        (ev368 := e4) (ev412 := e5) (ev442 := e6) (ev488 := e7) (ev558 := e8) (ev604 := e9)
        (sg723 := sg) (ev737 := e10) (op862 := op) (ev767 := evR) (hc864 := hc) .. =>
      rw [hnl] at ld
      obtain rfl := FamilyRecon.binop_add_one_nat op
      subst hc
      intro c hc1 hc2
      rcases Nat.eq_or_lt_of_le hc1 with rfl | hlt
      · exact ⟨h, m34, m144, m319, p41, xcty, _, _, _, _, _, _, _, cs47, cs329,
          Heap.Extends.refl _, e1, fun x hx => by simp [hx], ld, e2.heap_extends, e3, by simp⟩
      · have ih := check_inductive_shape_ctors_scoped hnc n (cidx + 1) (by omega) (by omega) evR
          c hlt hc2
        have e45 : Heap.Extends m319 m387 := by rw [hm]; exact Heap.Extends.snoc _ _
        have esg : Heap.Extends m592 m716 := by
          match sg with
          | .n0 (ev680 := ep) .. => exact ep.heap_extends
          | .other (he713 := hh) .. => rw [hh]
        exact ih.mono (fun x hx => by simp [hx])
          (e1.heap_extends.trans (e2.heap_extends.trans (e3.heap_extends.trans (e45.trans
            (e4.heap_extends.trans (e5.heap_extends.trans (e6.heap_extends.trans
              (e7.heap_extends.trans (e8.heap_extends.trans (e9.heap_extends.trans
                (esg.trans e10.heap_extends)))))))))))

/-- **`KernelCheck::check_const` on an inductive type loads and scope-checks every constructor of
it**, each at the inductive's level count: on the native route in
`KernelCheck::check_inductive_shape_ctors`, on the modeled route in
`KernelCheck::check_modeled_ctors`. -/
theorem check_const_induct_ctors_scoped {nctors : Nat} (hnc : nctors < 72057594037927936)
    {rc xnl xty xnp xni xu xblk xidx ap r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "KernelCheck::check_const"
      [rc, .construct "KernelTypes::KConstantInfo" "Induct"
        [xnl, xty, xnp, xni, .field (nctors : F), xu, xblk, xidx], ap] h r h' cs) :
    ∀ c, c < nctors → CtorScopedAt cs xblk xidx xnl h c := by
  cases Obs.«KernelCheck::check_const».obs ev with
  | Axiom_n1 | Axiom_other_n0 | Axiom_other_other
  | Defn | Thm | Opaque | Quot
  | Ctor_n0_n0 | Ctor_n0_other | Ctor_other_n0 | Ctor_other_other
  | Rec_n0 | Rec_other =>
    simp_all
  | Induct_n0 v1 m2 cs12 x_nlvls x_ty x_n_params x_n_indices x_num_ctors x_ind_is_unsafe
      x_ind_block x_ind_idx v1282 m1283 cs1293 v1330 m1333 cs1341 m1354 m1376 v1395 m1396 cs1406
      m1427 v1439 m1440 cs1450 v1469 m1470 cs1480 m1492 cs1503 v1518 m1519 cs1529 cs1607 ev14
      hne264 hne521 hne820 hne1071 hne1235 hv1240 ev1295 hm1362 hm1384 ev1343 heq1394 hm1435
      ev1408 ev1452 ev1482 ev1505 ev1531 ev1609 hc1634 =>
    simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv1240
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv1240
    have e1 : Heap.Extends m1283 m1376 := by rw [hm1384]; exact Heap.Extends.snoc _ _
    have e2 : Heap.Extends m1376 m1354 := by rw [hm1362]; exact Heap.Extends.snoc _ _
    have e3 : Heap.Extends m1333 m1427 := by rw [hm1435]; exact Heap.Extends.snoc _ _
    have ext : Heap.Extends h m1492 :=
      ev14.heap_extends.trans (ev1295.heap_extends.trans (e1.trans (e2.trans
        (ev1343.heap_extends.trans (e3.trans (ev1408.heap_extends.trans
          (ev1452.heap_extends.trans (ev1482.heap_extends.trans ev1505.heap_extends))))))))
    match Obs.«KernelCheck::check_inductive_shape».obs ev1531 with
    | .run (v1 := w1) (m2 := n2) (m50 := n50) (m63 := n63) (m133 := n133) (cs198 := ds)
        (hm58 := hm) (ev14 := f1) (ev75 := f2) (ev145 := f3) (ev200 := f4) (hc288 := hc) .. =>
      have e4 : Heap.Extends m1492 n50 := by rw [hm]; exact Heap.Extends.snoc _ _
      have f4' : ObsFn Obs.W "KernelCheck::check_inductive_shape_ctors"
          [rc, xty, xnp, xni, .field (nctors : F), xnl, xblk, xidx, w1, xu,
            .field ((0 : Nat) : F)] n133 v1518 m1519 ds := by
        rw [Nat.cast_zero]
        exact f4
      intro c hc'
      have hs := check_inductive_shape_ctors_scoped hnc nctors 0 rfl (Nat.zero_le _) f4' c
        (Nat.zero_le _) hc'
      exact hs.mono (fun x hx => by rw [hc1634, hc]; simp [hx])
        (ext.trans (e4.trans (f1.heap_extends.trans (f2.heap_extends.trans f3.heap_extends))))
  | Induct_other_n0 v1 m2 cs12 x_nlvls x_ty x_n_params x_n_indices x_num_ctors x_ind_block
      x_ind_idx v1282 m1283 cs1293 v1330 m1333 cs1341 m1354 m1376 v1395 m1396 cs1406 m1427 v1439
      m1440 cs1450 v1469 m1470 cs1480 v1491 m1492 cs1503 v1650 m1653 cs1661 v1698 m1701 cs1709
      v1746 m1749 cs1757 v1761 v1792 m1793 cs1803 v1808 m1841 v1853 m1854 cs1864 cs1955 ev14
      hne264 hne521 hne820 hne1071 hne1235 hv1240 ev1295 hm1362 hm1384 ev1343 heq1394 hm1435
      ev1408 ev1452 ev1482 ev1505 hne1635 ev1663 heq1686 ev1711 heq1734 op1782 ev1759 heq1791
      op1837 hm1849 ev1805 ev1866 ev1957 hc1974 =>
    simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv1240
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv1240
    have e1 : Heap.Extends m1283 m1376 := by rw [hm1384]; exact Heap.Extends.snoc _ _
    have e2 : Heap.Extends m1376 m1354 := by rw [hm1362]; exact Heap.Extends.snoc _ _
    have e3 : Heap.Extends m1333 m1427 := by rw [hm1435]; exact Heap.Extends.snoc _ _
    have e4 : Heap.Extends m1749 m1841 := by rw [hm1849]; exact Heap.Extends.snoc _ _
    have ext : Heap.Extends h m1793 :=
      ev14.heap_extends.trans (ev1295.heap_extends.trans (e1.trans (e2.trans
        (ev1343.heap_extends.trans (e3.trans (ev1408.heap_extends.trans
          (ev1452.heap_extends.trans (ev1482.heap_extends.trans (ev1505.heap_extends.trans
            (ev1663.heap_extends.trans (ev1711.heap_extends.trans (ev1759.heap_extends.trans
              (e4.trans ev1805.heap_extends)))))))))))))
    have f4' : ObsFn Obs.W "KernelCheck::check_modeled_ctors"
        [rc, xnp, xni, .field (nctors : F), xnl, xblk, xidx, .field 0,
          .field ((0 : Nat) : F)] m1793 v1853 m1854 cs1864 := by
      rw [Nat.cast_zero]
      exact ev1866
    intro c hc'
    have hs := check_modeled_ctors_scoped hnc nctors 0 rfl (Nat.zero_le _) f4' c
      (Nat.zero_le _) hc'
    exact hs.mono (fun x hx => by rw [hc1974]; simp [hx]) ext
  | Induct_other_other v1 m2 cs12 x_nlvls x_ty x_n_params x_n_indices x_num_ctors
      x_ind_is_unsafe x_ind_block x_ind_idx v1282 m1283 cs1293 v1330 m1333 cs1341 m1354 m1376
      v1395 m1396 cs1406 m1427 v1439 m1440 cs1450 v1469 m1470 cs1480 v1491 m1492 cs1503 v1650
      m1653 cs1661 v1698 m1701 cs1709 v1746 m1749 cs1757 v1761 v1792 m1793 cs1803 v1808 m1841
      v1853 m1854 cs1864 ev14 hne264 hne521 hne820 hne1071 hne1235 hv1240 ev1295 hm1362 hm1384
      ev1343 heq1394 hm1435 ev1408 ev1452 ev1482 ev1505 hne1635 ev1663 heq1686 ev1711 heq1734
      op1782 ev1759 heq1791 op1837 hm1849 ev1805 ev1866 hne1975 he1981 he1982 hc1983 =>
    simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv1240
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv1240
    have e1 : Heap.Extends m1283 m1376 := by rw [hm1384]; exact Heap.Extends.snoc _ _
    have e2 : Heap.Extends m1376 m1354 := by rw [hm1362]; exact Heap.Extends.snoc _ _
    have e3 : Heap.Extends m1333 m1427 := by rw [hm1435]; exact Heap.Extends.snoc _ _
    have e4 : Heap.Extends m1749 m1841 := by rw [hm1849]; exact Heap.Extends.snoc _ _
    have ext : Heap.Extends h m1793 :=
      ev14.heap_extends.trans (ev1295.heap_extends.trans (e1.trans (e2.trans
        (ev1343.heap_extends.trans (e3.trans (ev1408.heap_extends.trans
          (ev1452.heap_extends.trans (ev1482.heap_extends.trans (ev1505.heap_extends.trans
            (ev1663.heap_extends.trans (ev1711.heap_extends.trans (ev1759.heap_extends.trans
              (e4.trans ev1805.heap_extends)))))))))))))
    have f4' : ObsFn Obs.W "KernelCheck::check_modeled_ctors"
        [rc, xnp, xni, .field (nctors : F), xnl, xblk, xidx, xu,
          .field ((0 : Nat) : F)] m1793 v1853 m1854 cs1864 := by
      rw [Nat.cast_zero]
      exact ev1866
    intro c hc'
    have hs := check_modeled_ctors_scoped hnc nctors 0 rfl (Nat.zero_le _) f4' c
      (Nat.zero_le _) hc'
    exact hs.mono (fun x hx => by rw [hc1983]; simp [hx]) ext

private theorem natCast_inj32 {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296)
    (h : (.field (a : F) : SourceValue F) = .field (b : F)) : a = b := by
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  have := congrArg ZMod.val (Value.field.inj h)
  rw [SubstAux.val_natCast (by omega), SubstAux.val_natCast (by omega)] at this
  exact this

section CtorLevels

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env}

/-- **The readings of the constructors of an inductive type the run loaded and checked mention
only their level parameters** (`FamilyRecon.CtorLevelsDefinedAt` at the inductive's block and
position): `KernelCheck::check_const` loads each constructor of the inductive, asserts its level
count the inductive's and scopes its type at that count
(`check_const_induct_ctors_scoped`). -/
theorem ctorLevels_of_loadChecked (hS : LoadedReads.RunStore calls E₀) (hbd : Bounded calls)
    {a : _root_.Address} (hc : LoadChecked calls a) {cP : Ixon.Constant}
    {p : Ixon.InductiveProj} (hrecP : recordOf E₀ a = some cP) (hinfo : cP.info = .iPrj p) :
    ∀ c, CtorLevelsDefinedAt t E₀ p.block p.idx.toNat c := by
  obtain ⟨h, m, h', xa, pp, ci, rc, ap, r, cs, csc, ab, rfl, ha, ev, hsub, hld, evc, hsubc⟩ := hc
  intro c cb ms ind ct v hrecB hms hmem hct hread
  obtain ⟨rawBytes₂, c₂, hh₂, haddr₂, hex₂, -, hres₂⟩ :=
    L1.get_ci_block_trace_spec (RomBound.bounded_mono hbd hsub) ha ev
  have hc₂ : c₂ = cP := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hrecP)
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
        L1.repBoolField ind'.isUnsafe, blkPtr, .field (p.idx.toNat : F)] := hv
  rw [hshape] at evc
  have hclt : c < ind'.ctors.size := (Array.getElem?_eq_some_iff.mp hct).1
  obtain ⟨h1, m1, m2, m3, q, xcty, xb, xi, xc, xnp, xnf, xu, vv, cs1, csv, e0, evp, hcs1, ldc,
    e12, evs, hmemv⟩ := check_const_induct_ctors_scoped hnc evc c hclt
  have hb1 := Bytes.repAddressRef_heapMono₂ addrTy e0 hbrep
  have hsub1 : ∀ x ∈ cs1, x ∈ calls := fun x hx => hsubc x (hcs1 x hx)
  obtain ⟨-, -, -, blkBytes2, cb2, ms2, ind2, ct2, blobs2, v2, hhB2, haB2, hexB2, -, hcb2, hms2,
    hcts2, hhp2, hld2, hraw2⟩ := L1.get_ci_cprj_spec (RomBound.bounded_mono hbd hsub1) hb1 evp
  have hrecB' : recordOf E₀ (ixAddr b) = some cb' := by rw [hbaddr]; exact hrecB
  have f1 : cb2 = cb' := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hrecB')
    (Core.hashed_mono hsub1 hhB2) haB2 hexB2
  subst f1
  have f2 : ms2 = ms' := Ixon.ConstantInfo.muts.inj (hcb2.symm.trans hms)
  subst f2
  have f3 : ind2 = ind' := by
    rw [L1.val_cast_u56_ing hii, Array.getElem?_toList, hmem] at hms2
    exact (Ixon.MutConst.indc.inj (Option.some.inj hms2)).symm
  subst f3
  have f4 : ct2 = ct := by
    rw [L1.val_cast_u56_ing (Nat.lt_trans hclt hnc), Array.getElem?_toList, hct] at hcts2
    exact (Option.some.inj hcts2).symm
  subst f4
  obtain ⟨hl2, -, -, -, -, tyPtr2, blkPtr2, b2, -, -, hv2, rty2⟩ := hraw2
  have hsame := Except.ok.inj (hld2.symm.trans ldc)
  rw [hv2] at hsame
  have hargs := (Value.construct.inj hsame).2.2
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨g1, g2, -⟩ := hargs
  have hlv : ct2.lvls.toNat = ind2.lvls.toNat := natCast_inj32 hl2 hl g1
  subst g2
  have res := (Assembly.validate_expr_well_scoped_spec hbd hl rty2 e12 hread evs
    (hsubc _ hmemv)).2.2
  rw [hlv]
  exact res

/-- **The readings of the constructors of every inductive member of the block at `A` mention only
their level parameters.** -/
def UnitCtorLevelsAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (A : _root_.Address) : Prop :=
  ∀ i c, CtorLevelsDefinedAt t E A i c

/-- A record that is no block with an inductive member has no constructor reading. -/
theorem unitCtorLevelsAt_of_no_indc {E : Ixon.Env} {A : _root_.Address}
    (h : ∀ c, recordOf E A = some c → ∀ ms, c.info = .muts ms →
      ∀ m ∈ ms.toList, ∃ r, m = Ixon.MutConst.recr r) :
    UnitCtorLevelsAt t E A := by
  intro i c cb ms ind ct v hrec hms hm _ _
  have hmem : Ixon.MutConst.indc ind ∈ ms.toList :=
    List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hm)
  obtain ⟨r, hr⟩ := h cb hrec ms hms _ hmem
  cases hr

/-- **The constructor readings of a unit the run checked mention only their level parameters**
(`UnitCheckedAt`, at any context limit): every inductive member of a block checked member by
member, at its projection record's address. -/
theorem unitCtorLevelsAt_of_unitChecked (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀) (hbd : Bounded calls) {A : _root_.Address}
    {lim : Option Nat} (hu : UnitCheckedAt calls bAddr t E₀ A lim) :
    UnitCtorLevelsAt t E₀ A := by
  intro i c cb ms ind ct v hrec hms hm hct hread
  rcases hu with hc | ⟨cb', ms', hcb', hms', hall⟩
  · exact (Claim.checked_not_block hS hrec hms hc).elim
  · have e1 : cb' = cb := Option.some.inj (hcb'.symm.trans hrec)
    subst e1
    have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hms)
    subst e2
    have hklt : i < ms'.size := (Array.getElem?_eq_some_iff.mp hm).1
    obtain ⟨lc, hget, hx⟩ := recordOf_some hrec
    obtain ⟨cl, hcl, -, input, hargs, hrep⟩ := (hS.loaded.1 A lc hget).1
    have hlen : lc.rawBytes.data.toList.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbd hcl (by rw [hargs]; simp) hrep
    have hsize : lc.rawBytes.size = lc.rawBytes.data.toList.length := Array.length_toList.symm
    have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound lc.rawBytes cb' hx
    have hsz : ms'.size ≤ cb'.resourceSize := Claim.muts_size_le hms
    have hk58 : i < 288230376151711744 := by omega
    have hkk : i.toUInt64.toNat = i := by
      change (UInt64.ofNat i).toNat = i
      rw [UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (Nat.lt_trans hk58 (by decide))
    have hlc := LoadChecked.of_memberCheckedLim hk58 hm (hall i hklt)
    have hprec := (Claim.member_records hS hH hrec hms hm (hall i hklt)).1
    exact ctorLevels_of_loadChecked (t := t) hS hbd hlc hprec
      (p := ⟨i.toUInt64, A⟩) rfl c cb' ms' ind ct v hrec hms (by rw [hkk]; exact hm) hct hread

/-- **The constructor readings of a unit a group's admission adds, not stored before it, mention
only their level parameters**, for a bounded run with a collision-free store that validates every
role of the 77 groups: a unit with an inductive member is a record of the group's walk or a unit
reached through its payload, checked at the group's validation limit. -/
theorem unitCtorLevelsAt_of_added (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀) (hpin : PreludePinned t)
    (hcheck : t.check = .ok ()) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    {g : Nat} (hg6 : 6 ≤ g) (hg : g < 77) {A : _root_.Address}
    (hadd : GroupAdds t E₀ (runPayload calls bAddr t) g A)
    (hsb : ¬ StoredBelow t E₀ (runPayload calls bAddr t) g A) : UnitCtorLevelsAt t E₀ A := by
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
    exact unitCtorLevelsAt_of_no_indc (fun c hc => by rw [hrec] at hc; cases hc)
  | some c =>
    have hproj : IsProj c → UnitCtorLevelsAt t E₀ A := by
      intro hp
      refine unitCtorLevelsAt_of_no_indc (fun c' hc' ms hms => ?_)
      have e : c' = c := Option.some.inj (hc'.symm.trans hrec)
      subst e
      rcases hp with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ <;> (rw [hms] at hq; cases hq)
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
      exact unitCtorLevelsAt_of_unitChecked hS hH hbd (unitCheckedAt_of_topRec hH r)
    · have e : p = c := Option.some.inj (hp.symm.trans hrec)
      exact hproj (e ▸ hpr)
    · refine unitCtorLevelsAt_of_no_indc (fun c' hc' ms hms => ?_)
      have e : c' = c₂ := Option.some.inj (hc'.symm.trans hc₂)
      subst e
      rw [hms] at hinfo
      cases hinfo
    · rcases payAdds_cases hP hpay with ⟨hreach, -⟩ | ⟨-, -, -, -, -, p, hp, hpr, -⟩
      · by_cases hunit : UnitKind c ∧ ¬ IsTwinShape c
        · rcases payloadChecked_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
            g hg6 hg A c hreach hnew hcR' hunit.1 hunit.2 with hu | ⟨B, hfam, -⟩
          · exact unitCtorLevelsAt_of_unitChecked hS hH hbd hu
          · obtain ⟨-, -, cs, hfc⟩ := runFamOf_spec hfam
            obtain ⟨crb, rs, hcrb, -, hrs, hall, -⟩ := familyCall_record_block hS hH hfc
            refine unitCtorLevelsAt_of_no_indc (fun c' hc' ms hms => ?_)
            have e : c' = crb := Option.some.inj (hc'.symm.trans hcrb)
            subst e
            have e2 : ms = rs := Ixon.ConstantInfo.muts.inj (hms.symm.trans hrs)
            rw [e2]
            exact hall
        · refine unitCtorLevelsAt_of_no_indc (fun c' hc' ms hms => ?_)
          have e : c' = c := Option.some.inj (hc'.symm.trans hrec)
          subst e
          by_contra hcon
          refine hunit ⟨Or.inr (Or.inr ⟨ms, hms⟩), ?_⟩
          rintro ⟨rs, hrs, -, hall⟩
          have e2 : ms = rs := Ixon.ConstantInfo.muts.inj (hms.symm.trans hrs)
          exact hcon (e2 ▸ hall)
      · have e : p = c := Option.some.inj (hp.symm.trans hrec)
        exact hproj (e ▸ hpr)

/-- **The constructor readings of every unit stored before a group mention only their level
parameters**, given the same of the basis rows (`hbasisC`): every other stored unit is one a
group's admission adds (`unitCtorLevelsAt_of_added`). -/
theorem unitCtorLevelsAt_of_storedBelow (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀) (hpin : PreludePinned t)
    (hcheck : t.check = .ok ()) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    (hbasisC : ∀ A, (basisStore.consts.get? A).isSome = true → UnitCtorLevelsAt t E₀ A) :
    ∀ g, 6 ≤ g → g ≤ 77 → ∀ A, StoredBelow t E₀ (runPayload calls bAddr t) g A →
      UnitCtorLevelsAt t E₀ A := by
  intro g hg6
  induction g, hg6 using Nat.le_induction with
  | base =>
    intro _ A hA
    rcases hA with hbas | ⟨k, hk6, hk, -⟩
    · exact hbasisC A hbas
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
    exact unitCtorLevelsAt_of_added hC hbd hb hpin hcheck hstep hval hg6 (by omega) hadd hsb

/-- **The constructor readings of every block the store before a group holds mention only their
level parameters** (`FamilyRecon.CtorLevelsDefinedAt` at every position), under the hypotheses of
`unitCtorLevelsAt_of_storedBelow`. -/
theorem ctorLevelsDefinedAt_of_held (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀) (hpin : PreludePinned t)
    (hcheck : t.check = .ok ()) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    (hbasisC : ∀ A, (basisStore.consts.get? A).isSome = true → UnitCtorLevelsAt t E₀ A)
    {g : Nat} (hg6 : 6 ≤ g) (hg : g ≤ 77) {b : _root_.Address}
    (hheld : Held (groupStore t E₀ (runPayload calls bAddr t) g) b) :
    ∀ i c, CtorLevelsDefinedAt t E₀ b i c := by
  obtain ⟨c₀, hc₀⟩ := Option.isSome_iff_exists.mp hheld
  obtain ⟨hsb, -⟩ := (groupStore_recordOf hb hg6).mp hc₀
  exact unitCtorLevelsAt_of_storedBelow hC hbd hb hpin hcheck hstep hval hbasisC g hg6 hg b hsb

/-- **Every `Ingress::get_ci_cprj` among the calls `cs` at a block the store `E` has a record at
is at a block of `S`.** -/
def CprjLoadsIn (E : Ixon.Env) (cs : List (Call F)) (S : _root_.Address → Prop) : Prop :=
  ∀ {xblk : SourceValue F} {h : Heap F} {ba : Bytes.Address} {i c : Nat},
    i < 72057594037927936 → c < 72057594037927936 →
    (⟨"Ingress::get_ci_cprj", [xblk, .field (i : F), .field (c : F)], h⟩ : Call F) ∈ cs →
    Bytes.RepAddressRef addrTy h ba xblk →
    (recordOf E (ixAddr ba)).isSome = true → S (ixAddr ba)

/-- **The readings of the constructors the calls `cs` load mention only their level parameters**
(`FamilyRecon.CprjLevelsDefined`), when `cs` loads constructors only of blocks the store after
group `g` holds (`CprjLoadsIn`), given the same of the basis rows (`hbasisC`). -/
theorem cprjLevelsDefined_of_loadsIn (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀) (hpin : PreludePinned t)
    (hcheck : t.check = .ok ()) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    (hbasisC : ∀ A, (basisStore.consts.get? A).isSome = true → UnitCtorLevelsAt t E₀ A)
    {g : Nat} (hg6 : 6 ≤ g) (hg : g < 77) {cs : List (Call F)}
    (hin : CprjLoadsIn E₀ cs (Held (groupStore t E₀ (runPayload calls bAddr t) (g + 1)))) :
    CprjLevelsDefined t E₀ cs := by
  intro xblk h ba i c hi hc hm hb'
  cases hrec : recordOf E₀ (ixAddr ba) with
  | none =>
    intro cb ms ind ct v hr
    rw [hrec] at hr
    cases hr
  | some c0 =>
    exact ctorLevelsDefinedAt_of_held hC hbd hb hpin hcheck hstep hval hbasisC
      (Nat.le_succ_of_le hg6) hg (hin hi hc hm hb' (by rw [hrec]; rfl)) i c

/-- **The store answers of a selected family's check, from the run**: for a bounded run with a
collision-free store that validates every role of the 77 groups and hashes no collision with its
store, and a family check of a block selected at group `g`, every store answer the reconstruction
and the flattening read holds for the check's calls `cs`, the flattening's constructor answer at
the blocks the store after the group holds, which is closed under what both read
(`SelectedStore`). What is asked beyond the run: that the readings of the basis rows mention only
their level parameters (`hbasis`, `hbasisC`), and that the check loads constants and constructors
only at addresses the store after the group holds (`hin`, `hcin`). -/
theorem familyCallAnswers_of_selected (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀) (hpin : PreludePinned t)
    (hcheck : t.check = .ok ()) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    (hnc : ¬ View.HashedCollision { env := E₀ } [] calls)
    (hbasis : ∀ A, (basisStore.consts.get? A).isSome = true → UnitLevelsAt t E₀ A)
    (hbasisC : ∀ A, (basisStore.consts.get? A).isSome = true → UnitCtorLevelsAt t E₀ A)
    {g : Nat} (hg6 : 6 ≤ g) (hg : g < 77) {B rb : _root_.Address}
    (hf : runFamOf calls bAddr t E₀ g B = some rb) {lim : Option Nat} {cs : List (Call F)}
    (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs)
    (hin : LoadsIn E₀ cs (Held (groupStore t E₀ (runPayload calls bAddr t) (g + 1))))
    (hcin : CprjLoadsIn E₀ cs (Held (groupStore t E₀ (runPayload calls bAddr t) (g + 1)))) :
    FamilyCallAnswers t E₀ cs (Held (groupStore t E₀ (runPayload calls bAddr t) (g + 1))) ∧
    SelectedStore t E₀ (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B rb :=
  ⟨familyCallAnswers hcheck hC.runStore hC.hashedStored hbd hnc hfc
      (loadedLevelsDefined_of_loadsIn hC hbd hb hpin hcheck hstep hval hbasis hg6 hg hin)
      (cprjLevelsDefined_of_loadsIn hC hbd hb hpin hcheck hstep hval hbasisC hg6 hg hcin)
      (fun b hb' => ctorLevelsDefinedAt_of_held hC hbd hb hpin hcheck hstep hval hbasisC
        (Nat.le_succ_of_le hg6) hg hb'),
    selectedStore_of_run hC hbd hb hpin hcheck hstep hval hg6 hg hf⟩

end CtorLevels

end IxVM.Refinement.Binding.FamilyLoadAnswers
