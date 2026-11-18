import IxVMRefinement.Guard.CheckedFields
import IxVMRefinement.Guard.CtorRaw
import IxVMRefinement.Assembly.GuardRawRoots
import IxVMRefinement.StatementRel.LoadedReadsWalked
import IxVMRefinement.Assembly.TypingDefnStep

/-! # The checked field loop read over the run's store

`GuardData.CheckedFieldsAt` keeps, with the sorts the field loop checked, the raw telescope the
loop walked and the classifier's field traces over the loop's own declared-type and definition
loads. This module reads those loads in the raw dictionary of a store that holds what the run
hashed, and so turns the traces into the classifier function over that store.

The store is the run's (`LoadedReads.RunStore`, `LoadedReads.HashedRecordsStored`): two byte
strings the run hashed under one address are equal there, so a load decodes the store's record
and no collision alternative remains.

* `LoadParentsHeld calls E`: the store holds the block of every projection record the run
  loads through `Ingress::get_ci`. The one fact about the store used here that the two run
  store facts do not give as they stand (they cover hashed records below `2^32` bytes; the
  loader's bound on the block it reads is not exported by the load's specification).
* `typeAnswer_runStore`, `valueAnswer_runStore`: a declared-type or definition answer of a
  trace is the store's dictionary answer, with metadata erased.
* `ctorRaw_runStore`: the telescope the loop walked is the dictionary's reading of the
  constructor's type in the block record.
* `CheckedSortsReadingAt calls E`: the reading of the checked field loop over the store `E`:
  the hypotheses of `Guard.projGuardCert_of_checkNativeTable` for the sorts of
  `CheckedFieldsAt`. `checkedSortsReadingAt_runStore` proves it over the run's store;
  `CheckedSortsReadingAt.stepStore` moves it to any store that holds the run store's records
  and blobs.
-/

namespace IxVM.Refinement.Guard

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open IxVM.Refinement.Core
open IxVM.Refinement.Decl (RawExprRep RawTypeAt RawDeltaAt RawFieldTraces)

set_option maxHeartbeats 1600000

/-- The block a projection record names. -/
def projBlock : Ixon.ConstantInfo → Option _root_.Address
  | .dPrj p => some p.block
  | .iPrj p => some p.block
  | .cPrj p => some p.block
  | .rPrj p => some p.block
  | _ => none

/-- **The store holds the block of every projection record the run loads** (module
docstring). -/
def LoadParentsHeld (calls : List (Call F)) (E : Ixon.Env) : Prop :=
  ∀ (a : Bytes.Address) (ap ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
    (c : Ixon.Constant) (B : _root_.Address),
    (∀ cl ∈ cs, cl ∈ calls) → Bytes.RepAddressRef addrTy h a ap →
    ObsFn W "Ingress::get_ci" [ap] h ptr h' cs →
    Ix.Cert.recordAt E (ixAddr a) = some c → projBlock c.info = some B →
    (E.consts.get? B).isSome

/-- A block entry of a load's own store is the run store's entry at that address, where the
run store holds one. -/
private theorem parent_entry {calls cs : List (Call F)} {E E_ld : Ixon.Env}
    (hS : LoadedReads.RunStore calls E) (hload : LoadedBy cs E_ld)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) {k : _root_.Address} {lcB : Ixon.LazyConstant}
    {cb : Ixon.Constant} (hheld : (E.consts.get? k).isSome)
    (hget : E_ld.consts.get? k = some lcB)
    (hex : Ixon.deConstantExact lcB.rawBytes = .ok cb)
    (hde : Ixon.deConstant lcB.rawBytes = .ok cb) :
    ∃ lc', E.consts.get? k = some lc' ∧ lc'.get? = some cb ∧
      Ix.Cert.recordAt E k = some cb ∧ Ixon.deConstantExact lc'.rawBytes = .ok cb ∧
      Ixon.deConstant lc'.rawBytes = .ok cb := by
  obtain ⟨lc', hget'⟩ := Option.isSome_iff_exists.mp hheld
  obtain ⟨hhB, haB⟩ := hload.1 k lcB hget
  obtain ⟨hh', ha'⟩ := hS.loaded.1 k lc' hget'
  have hbytes : lcB.rawBytes = lc'.rawBytes :=
    hS.hashed_inj (Core.hashed_mono hsub hhB) hh' (haB.trans ha'.symm)
  obtain ⟨c₀, hc₀, hex₀⟩ := hS.decoded k lc' hget'
  rw [hbytes] at hex hde
  have hc : c₀ = cb := Except.ok.inj (hex₀.symm.trans hex)
  subst hc
  refine ⟨lc', hget', hc₀, ?_, hex, hde⟩
  unfold Ix.Cert.recordAt
  rw [hget']
  exact hc₀

/-- **A load's raw payload, read against the run's store**: the blobs it hashed are the run
store's, and the block of a projection record is the run store's record where the store holds
one. -/
theorem rawCIRep_runStore {calls cs : List (Call F)} {E E_ld : Ixon.Env}
    (hS : LoadedReads.RunStore calls E) (hload : LoadedBy cs E_ld)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) {h : Heap F} {a : _root_.Address} {c : Ixon.Constant}
    {v : SourceValue F}
    (hparent : ∀ B, projBlock c.info = some B → (E.consts.get? B).isSome)
    (raw : L1.RawCIRep E_ld h a c v) : L1.RawCIRep E h a c v := by
  have blobs : ∀ {table : List (_root_.Address × ByteArray)},
      L1.BlobTableLoaded E_ld table → L1.BlobTableLoaded E table := by
    intro table loaded
    refine Or.inl fun x bs member => ?_
    have held := hS.blob_of_table hload hsub loaded x bs member
    exact ⟨held, (hS.loaded.2 x bs held).2⟩
  unfold L1.RawCIRep at raw ⊢
  cases hc : c.info with
  | defn d =>
    rw [hc] at raw
    obtain ⟨table, hb, hraw⟩ := raw
    exact ⟨table, blobs hb, hraw⟩
  | axio ax =>
    rw [hc] at raw
    obtain ⟨table, hb, hraw⟩ := raw
    exact ⟨table, blobs hb, hraw⟩
  | quot q =>
    rw [hc] at raw
    obtain ⟨table, hb, hraw⟩ := raw
    exact ⟨table, blobs hb, hraw⟩
  | recr rc =>
    rw [hc] at raw
    obtain ⟨table, hb, hraw⟩ := raw
    exact ⟨table, blobs hb, hraw⟩
  | dPrj p =>
    rw [hc] at raw hparent
    obtain ⟨hidx, lcB, cb, ms, d, table, hget, -, -, hex, hde, hms, hm, hb, hraw⟩ := raw
    obtain ⟨lc', hget', hcache', hrec', hex', hde'⟩ :=
      parent_entry hS hload hsub (hparent p.block rfl) hget hex hde
    exact ⟨hidx, lc', cb, ms, d, table, hget', hcache', hrec', hex', hde', hms, hm, blobs hb,
      hraw⟩
  | iPrj p =>
    rw [hc] at raw hparent
    obtain ⟨hidx, lcB, cb, ms, ind, table, hget, -, -, hex, hde, hms, hm, hb, hraw⟩ := raw
    obtain ⟨lc', hget', hcache', hrec', hex', hde'⟩ :=
      parent_entry hS hload hsub (hparent p.block rfl) hget hex hde
    exact ⟨hidx, lc', cb, ms, ind, table, hget', hcache', hrec', hex', hde', hms, hm, blobs hb,
      hraw⟩
  | cPrj p =>
    rw [hc] at raw hparent
    obtain ⟨hidx, hcidx, lcB, cb, ms, ind, ct, table, hget, -, -, hex, hde, hms, hm, hct, hb,
      hraw⟩ := raw
    obtain ⟨lc', hget', hcache', hrec', hex', hde'⟩ :=
      parent_entry hS hload hsub (hparent p.block rfl) hget hex hde
    exact ⟨hidx, hcidx, lc', cb, ms, ind, ct, table, hget', hcache', hrec', hex', hde', hms, hm,
      hct, blobs hb, hraw⟩
  | rPrj p =>
    rw [hc] at raw hparent
    obtain ⟨hidx, lcB, cb, ms, rc, table, hget, -, -, hex, hde, hms, hm, hb, hraw⟩ := raw
    obtain ⟨lc', hget', hcache', hrec', hex', hde'⟩ :=
      parent_entry hS hload hsub (hparent p.block rfl) hget hex hde
    exact ⟨hidx, lc', cb, ms, rc, table, hget', hcache', hrec', hex', hde', hms, hm, blobs hb,
      hraw⟩
  | muts ms =>
    rw [hc] at raw
    exact raw.elim

/-- **A load of the run, as the run store's raw payload**: the record the store holds at the
loaded address, and the payload the load returned as that record's raw conversion over the
store. -/
theorem get_ci_rawCIRep_runStore {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (hpar : LoadParentsHeld calls E₀) {address : Bytes.Address} {ap ptr value : SourceValue F}
    {before loaded : Heap F} {loadCalls : List (Call F)}
    (hbound : IxVM.Consistency.Bounded loadCalls) (hsub : ∀ cl ∈ loadCalls, cl ∈ calls)
    (addressRep : Bytes.RepAddressRef addrTy before address ap)
    (load : ObsFn W "Ingress::get_ci" [ap] before ptr loaded loadCalls)
    (node : loadValue loaded ptr = .ok value) :
    ∃ record, recordOf E₀ (ixAddr address) = some record ∧
      L1.RawCIRep E₀ loaded (ixAddr address) record value := by
  obtain ⟨-, bytes, E_ld, hashed, hashAddress, loadedBy, loadedL1⟩ :=
    L1.get_ci_loadedL1_spec hbound addressRep load
  obtain ⟨record, stored⟩ :=
    LoadedReads.recordAt_of_get_ci hcov ⟨address, addressRep, rfl⟩ load hsub
  obtain ⟨-, -, v, loadedValue, rawCI⟩ :=
    LoadedReads.loadedL1_record hS hsub hashed hashAddress loadedL1 stored
  rw [node] at loadedValue
  have sameValue : value = v := Except.ok.inj loadedValue
  subst sameValue
  exact ⟨record, hS.recordOf_of_recordAt stored,
    rawCIRep_runStore hS loadedBy hsub
      (fun B block =>
        hpar address ap ptr before loaded loadCalls record B hsub addressRep load stored block)
      rawCI⟩

/-- **A declared-type answer of a trace is the run store's dictionary answer**, with its
metadata erased. -/
theorem typeAnswer_runStore {c : ScopedCtx} {calls rootCalls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (hpar : LoadParentsHeld calls E₀) (hbound : IxVM.Consistency.Bounded rootCalls)
    (hsub : ∀ cl ∈ rootCalls, cl ∈ calls)
    {key : KKey} {ps : List KLevel} {out : KExpr}
    (answer : RawTypeAt c (Core.keyOf GuardRaw.addressTable) rootCalls key ps out) :
    (GuardRaw.ofStore E₀).typeOf key ps = some out.eraseMeta := by
  obtain ⟨address, ci, raw, ap, ptr, value, typePtr, before, loaded, beforeType, beforeInst,
    loadCalls, typeCalls, rfl, -, -, addressRep, load, -, node, getType, extension,
    ⟨image, physical⟩, loadSubset, -, rfl, small, beforeCount, afterCount, countCalls,
    counted⟩ := answer
  obtain ⟨record, stored, rawCI⟩ := get_ci_rawCIRep_runStore hS hcov hpar
    (bounded_sub loadSubset hbound) (fun cl member => hsub cl (loadSubset cl member))
    addressRep load node
  obtain ⟨countPtr, countFields, -⟩ := GuardRaw.const_count_fields counted
  obtain ⟨count, typeFields, -⟩ := GuardRaw.const_type_fields getType
  have same := countFields.symm.trans typeFields
  have pointer : countPtr = typePtr := (Prod.mk.inj (Option.some.inj same)).2
  rw [pointer] at countFields
  rcases GuardRaw.type_lookup_exact stored (L1.RawCIRep.mono extension rawCI) physical
    countFields small with collision | found
  · exact absurd collision hS.no_internal_collision
  · exact found

/-- **A definition answer of a trace is the run store's dictionary answer**, with its metadata
erased. -/
theorem valueAnswer_runStore {c : ScopedCtx} {calls rootCalls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (hpar : LoadParentsHeld calls E₀) (hbound : IxVM.Consistency.Bounded rootCalls)
    (hsub : ∀ cl ∈ rootCalls, cl ∈ calls)
    {key : KKey} {ps : List KLevel} {out : KExpr}
    (answer : RawDeltaAt c (Core.keyOf GuardRaw.addressTable) rootCalls key ps out) :
    (GuardRaw.ofStore E₀).valueOf key ps = some out.eraseMeta := by
  obtain ⟨address, cv, body, raw, hint, ap, ptr, levels, ty, value, safety, hintPtr, before,
    loaded, loadCalls, rfl, -, -, addressRep, load, -, node, ⟨image, physical⟩, loadSubset, rfl,
    arity, small⟩ := answer
  obtain ⟨record, stored, rawCI⟩ := get_ci_rawCIRep_runStore hS hcov hpar
    (bounded_sub loadSubset hbound) (fun cl member => hsub cl (loadSubset cl member))
    addressRep load node
  rcases GuardRaw.value_lookup_exact stored rfl rawCI physical arity small with
    collision | found
  · exact absurd collision hS.no_internal_collision
  · exact found

/-- The constructor load begins with its verified read of the block. -/
theorem get_ci_cprj_verified_subcall {bp ptr : SourceValue F} {i j : F} {h h' : Heap F}
    {calls : List (Call F)}
    (observed : ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field j] h ptr h' calls) :
    ∃ value middle children,
      ObsFn W "Ingress::load_verified_constant" [bp] h value middle children ∧
      ∀ call ∈ children, call ∈ calls := by
  match Obs.«Ingress::get_ci_cprj».obs observed with
  | .run (ev14 := loaded) (hc381 := allCalls) .. =>
    exact ⟨_, _, _, loaded, by rw [allCalls]; intro call member; simp [member]⟩

/-- **The telescope the field loop walked is the dictionary's reading of the constructor's
type**: the type pointer of the constructor payload a `get_ci_cprj` load returned, read as raw
syntax under address keys, is `ctorRaw` of the run's store at the block and the member, with
its metadata erased. -/
theorem ctorRaw_runStore {calls cs₀ : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (hbound : IxVM.Consistency.Bounded cs₀) (hsub : ∀ cl ∈ cs₀, cl ∈ calls)
    {b : Bytes.Address} {i : F} {bp ptr p w₁ w₃ w₄ w₅ w₆ w₇ w₈ : SourceValue F}
    {h₀ m h : Heap F}
    (load : ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field 0] h₀ ptr m cs₀)
    (hb : Bytes.RepAddressRef addrTy h₀ b bp)
    (ld : loadValue m ptr = .ok (.construct kciEnum "Ctor" [w₁, p, w₃, w₄, w₅, w₆, w₇, w₈]))
    (hext : Heap.Extends m h) {k : Nat} {R : KExpr}
    (physical : RawExprRep (Core.keyOf GuardRaw.addressTable) h k R p) :
    Guard.ctorRaw E₀ (ixAddr b) (ZMod.val i) 0 = some R.eraseMeta := by
  obtain ⟨-, -, -, blkBytes, cb, ms, ind, ct, table, v, hashedBlock, blockAddress, exact,
    -, shape, member, constructor, hashedBlobs, loadedValue, rawCtor⟩ :=
    L1.get_ci_cprj_spec hbound hb load
  -- the run's store holds the block the load read
  obtain ⟨value, middle, children, verified, verifiedSub⟩ := get_ci_cprj_verified_subcall load
  obtain ⟨-, bytes, c', size, hashed', address', exact', decoded', -⟩ :=
    L1.load_verified_constant_decode_bounded hb verified
  have hashedRun' : Hashed calls ⟨bytes.toArray⟩ :=
    Core.hashed_mono (fun cl member => hsub cl (verifiedSub cl member)) hashed'
  obtain ⟨lc, stored, bytesEq, -⟩ := hcov ⟨bytes.toArray⟩ c' hashedRun'
    (by simpa only [ByteArray.size, List.size_toArray] using size) decoded' exact'
  have sameBytes : blkBytes = ⟨bytes.toArray⟩ :=
    hS.hashed_inj (Core.hashed_mono hsub hashedBlock) hashedRun'
      (blockAddress.trans address'.symm)
  have record : recordOf E₀ (ixAddr b) = some cb := by
    have sameAddress : Address.blake3Pure ⟨bytes.toArray⟩ = ixAddr b := address'
    have held : E₀.consts.get? (ixAddr b) = some lc := by rw [← sameAddress]; exact stored
    apply Typing.recordOf_of_get held
    rw [bytesEq, ← sameBytes]
    exact exact
  -- the payload's type pointer is the block's constructor type, converted
  obtain ⟨-, -, -, -, -, tyPtr, blkPtr, b', -, -, valueShape, converted⟩ :=
    rawCtor.mono hext (fun _ belongs => belongs)
  have sameValue := Except.ok.inj (loadedValue.symm.trans ld)
  rw [valueShape] at sameValue
  injection sameValue with _ _ fields
  injection fields with _ rest
  injection rest with pointer _
  subst pointer
  obtain ⟨image, exactRep⟩ := physical
  have member' : ms[ZMod.val i]? = some (.indc ind) := by
    simpa only [Array.getElem?_toList] using member
  have ctor' : ind.ctors[0]? = some ct := by
    simpa only [Array.getElem?_toList, ZMod.val_zero] using constructor
  let root : GuardRaw.Root := ⟨cb, blockSelf GuardRaw.addressTable (ixAddr b) ms,
    L1.mutsRootOffset ms.toList (ZMod.val i) + (1 + 0), ct.lvls.toNat, ct.typ⟩
  have selected : GuardRaw.memberRoot (recordOf E₀) (ixAddr b) (ZMod.val i)
      (GuardRaw.constructorType 0) = some root := by
    simp [GuardRaw.memberRoot, record, shape, member', GuardRaw.constructorType, ctor', root]
  have rootConverted : GuardRaw.RootConverted (fun x => E₀.blobs.get? x) root h tyPtr :=
    ⟨_, table, converted, LoadedReads.blockSelf_ok GuardRaw.addressTable (ixAddr b) ms,
      LoadedReads.blockSelf_key GuardRaw.addressTable (ixAddr b) ms,
      fun x bs belongs => by
        obtain ⟨hashedBlob, blobAddress⟩ := hashedBlobs (x, bs) belongs
        have held := hS.blobs bs (Core.hashed_mono hsub hashedBlob)
        rw [blobAddress] at held
        exact held⟩
  have read := rootConverted.exact exactRep
  unfold Guard.ctorRaw
  rw [selected]
  exact read

/-- **The reading of the checked field loop over the store `E`**, for the sorts the loop
checked: the constructor's raw telescope read from `E`, the classifier's signatures of its
fields over `E`'s raw dictionary, and the zero-set agreement of each sort with its field's
signature. These are the hypotheses of `Guard.projGuardCert_of_checkNativeTable`. -/
def CheckedSortsReadingAt (calls : List (Call F)) (E : Ixon.Env) : Prop :=
  ∀ (c : ScopedCtx) {b : Bytes.Address} {i : F} {nP nF : Nat} {cty : KExpr} {u : KLevel}
    {sorts : List KLevel},
    GuardData.CheckedFieldsAt c calls b i nP nF cty u sorts →
    ∃ (sigs : List KLevel) (fuel : Nat) (raw : KExpr),
      Guard.ctorRaw E (ixAddr b) (ZMod.val i) 0 = some raw ∧
      Ix.Kernel.GuardClassifier.fieldSignatures (GuardRaw.ofStore E) fuel nP nF [] raw =
        some sigs ∧
      ∀ j, j < nF → ∀ φ : Ix.Kernel.LevelParam → Nat,
        Ix.Kernel.Level.eval φ (sorts.getD j .zero) = 0 ↔
          Ix.Kernel.Level.eval φ (sigs.getD j .zero) = 0

/-- **The reading holds over the run's store.** -/
theorem checkedSortsReadingAt_runStore {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (hpar : LoadParentsHeld calls E₀) : CheckedSortsReadingAt calls E₀ := by
  intro c b i nP nF cty u sorts checked
  obtain ⟨Γ, residual, body, parameters, fvs, rc, level, p, r, np, nf, h, h', cs, bp, ptr,
    w₁, w₃, w₄, w₅, w₆, w₇, w₈, h₀, m, cs₀, -, -, -, -, good, -, -, -, -, -, load, good₀, hb,
    ld, hext, inside, inside₀, -, R, signatures, physical, traces, zeros⟩ := checked
  obtain ⟨fuel, walked⟩ := traces.fieldSignatures_erased
    (look := GuardRaw.ofStore E₀)
    (fun _ _ _ answer => typeAnswer_runStore hS hcov hpar good.bounded inside answer)
    (fun _ _ _ answer => valueAnswer_runStore hS hcov hpar good.bounded inside answer)
  exact ⟨signatures, fuel, R.eraseMeta,
    ctorRaw_runStore hS hcov good₀.bounded inside₀ load hb ld hext physical, walked, zeros⟩

/-- **The reading moves to a store that holds the run store's records and blobs**: the raw
dictionary only extends, and the classifier's answer and the telescope's reading are kept by
an extension. -/
theorem CheckedSortsReadingAt.stepStore {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} (hst : Typing.StepStore calls t E₀ E)
    (reading : CheckedSortsReadingAt calls E₀) : CheckedSortsReadingAt calls E := by
  intro c b i nP nF cty u sorts checked
  obtain ⟨sigs, fuel, raw, hraw, hsig, hzeros⟩ := reading c checked
  have records : ∀ a rec, recordOf E₀ a = some rec → recordOf E a = some rec :=
    fun _ _ held => hst.held held
  refine ⟨sigs, fuel, raw, ?_,
    Ix.Kernel.GuardClassifier.fieldSignatures_mono
      (GuardRaw.lookup_extends records hst.runBlob) (Nat.le_refl fuel) hsig, hzeros⟩
  unfold Guard.ctorRaw at hraw ⊢
  obtain ⟨root, hroot, hread⟩ := Option.bind_eq_some_iff.mp hraw
  exact Option.bind_eq_some_iff.mpr
    ⟨root, GuardRaw.memberRoot_mono records hroot, GuardRaw.readRoot_mono hst.runBlob hread⟩

/-- **The reading of the checked field loops at one block**: `CheckedSortsReadingAt` asked only of
the loops whose block is `B`. A store that holds `B` and what the loops at `B` load has it,
whatever it lacks of the records the loops at other blocks load. -/
def CheckedSortsReadingAtBlock (calls : List (Call F)) (E : Ixon.Env) (B : _root_.Address) :
    Prop :=
  ∀ (c : ScopedCtx) {b : Bytes.Address} {i : F} {nP nF : Nat} {cty : KExpr} {u : KLevel}
    {sorts : List KLevel},
    GuardData.CheckedFieldsAt c calls b i nP nF cty u sorts → Core.ixAddr b = B →
    ∃ (sigs : List KLevel) (fuel : Nat) (raw : KExpr),
      Guard.ctorRaw E (ixAddr b) (ZMod.val i) 0 = some raw ∧
      Ix.Kernel.GuardClassifier.fieldSignatures (GuardRaw.ofStore E) fuel nP nF [] raw =
        some sigs ∧
      ∀ j, j < nF → ∀ φ : Ix.Kernel.LevelParam → Nat,
        Ix.Kernel.Level.eval φ (sorts.getD j .zero) = 0 ↔
          Ix.Kernel.Level.eval φ (sigs.getD j .zero) = 0

/-- The reading of every loop gives the reading of the loops at any one block. -/
theorem CheckedSortsReadingAt.block {calls : List (Call F)} {E : Ixon.Env}
    (reading : CheckedSortsReadingAt calls E) (B : _root_.Address) :
    CheckedSortsReadingAtBlock calls E B :=
  fun c _ _ _ _ _ _ _ checked _ => reading c checked

end IxVM.Refinement.Guard
