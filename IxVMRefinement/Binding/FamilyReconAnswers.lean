import IxVMRefinement.Binding.FamilyReconWhnf
import IxVMRefinement.Binding.FamilyReconStore
import IxVMRefinement.StatementRel.LoadedReadsBlockTrace
import IxVMRefinement.StatementRel.LoadedReadsWalked
import IxVMRefinement.Claim.RefSafety
import IxVMRefinement.Guard.LoadParents

/-! # The reconstruction's store answers, for the calls of a run

The leaf specifications of the reconstruction (`FamilyReconWhnf`, `FamilyReconSites`,
`FamilyReconFlat`) read the store through five single-call predicates (`AddrOf`, `DefnAnswers`,
`IndAnswers`, `CtorOfAnswers`, `ModeledAnswers`). This module produces them at the view of a run's
store (`ReconView.ofStore t E₀`), in the form a run determines:

* `AddrOf (keyOf t) (ReconView.ofStore t E₀)` holds outright at a well-formed table
  (`addrOf_ofStore`).
* The four load predicates (`ModeledAnswers`, `CtorOfAnswers`, `DefnAnswers`, `IndAnswers`) carry
  the run's calls and ask the answer only of an observation whose calls are among them. A run
  determines only the loads among its own calls: the run's store holds a record at an address only
  where the run hashed one, and the hash is injective only on what the run hashed.
* The load's specification (`L1.RawInductValRep`, `L1.RawCtorValRep`) bounds a loaded inductive's
  parameter, index and constructor counts and position, and a loaded constructor's parameter and
  field counts, by `2^56`, not `2^32`. `IndAnswers` and `CtorOfAnswers` state those bounds.
* A loaded definition's value and a loaded inductive's type are represented exactly, as the open
  term the model reads (`FamilyFlat.loadedAt`, by `loadedAt_tmOExact`), where the reading mentions
  only the constant's own level parameters (`LevelsDefinedAt`): the exact correspondence of the
  conversion with the reader (`L1.RawConvExpr.toTmExactTrace_of_blobAgreement`) is stated for
  defined level parameters. No scoping of bound variables and no safety of the record is asked.
  `DefnAnswers` and `IndAnswers` answer for a load that is itself one of the run's calls, and
  their producers ask `LevelsDefinedAt` at the addresses the run loads (`LoadedLevelsDefined`).

`defnAt_of_load` and `indDataAt_of_load` are the single-load forms against the store's own
readings (`defnAt`, `indDataAt`); `storeAnswers_of_run` bundles the five for a bounded run with
its store; `storeNoCollision_of_view` gives the store-level no-collision the dispatch asks from
a view's. `defnValAt_of_defnAt` reads a definition of the store as the flattening's lookup of it
(`FamilyFlat.defnValAt`). -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency
open IxVM.Refinement.Core (W KExpr KLevel KKey kexprEnum addrTy ixAddr)
open IxVM.Refinement.Binding.FamilyFlat (exprInstLevels loadedAt mutsRoot keyAddr keyAddr_keyOf)
open IxVM (F)

set_option linter.unusedVariables false

/-! ## The key-address map -/

/-- **The view of a store inverts the table's keying**, at a well-formed table. -/
theorem addrOf_ofStore {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) (E : Ixon.Env) :
    AddrOf (keyOf t) (ReconView.ofStore t E) :=
  fun a => keyAddr_keyOf hwf a

/-! ## The modeled-route test -/

section Run

variable {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}

/-- A run's store holds, with its exact decoding, every record a sub-derivation hashed. -/
theorem canonicalHashCoverage_of_run (hH : LoadedReads.HashedRecordsStored calls E₀)
    {cs : List (Call F)} (hsub : ∀ c ∈ cs, c ∈ calls) : L1.CanonicalHashCoverage E₀ cs := by
  intro bytes value hashed size exactRead
  obtain ⟨entry, stored, bytesEq, cached⟩ := hH bytes value (Core.hashed_mono hsub hashed) size
    (L1.deConstant_of_deConstantExact exactRead) exactRead
  refine ⟨⟨entry, value, stored, cached, ?_⟩, rfl⟩
  rw [bytesEq]
  exact exactRead

/-- **`ModeledAnswers` of a run**: among the calls of a bounded run that hashes no collision
with its store, the dispatch answers `Route.blockRoute` of the store, known at every block it is
asked of (`Route.block_is_modeled_agrees`). -/
theorem modeledAnswers_of_run (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls) (hnc : ¬ View.HashedCollision { env := E₀ } [] calls) :
    ModeledAnswers calls (ReconView.ofStore t E₀) := by
  intro xblk r h m cs ba hb ev hsub
  have hnc' : ¬ View.HashedCollision { env := E₀ } [] cs :=
    fun hc => hnc (Claim.hashedCollision_mono hsub hc)
  have ag := Route.block_is_modeled_agrees hnc' (RomBound.bounded_mono hbd hsub) hb ev
  obtain ⟨v, hv⟩ := ag.known (canonicalHashCoverage_of_run hH hsub)
  refine ⟨v, hv, ?_⟩
  have hr := ag.value v hv
  rw [hr]
  cases v <;> rfl

/-! ## The constructor tag of a loaded constant -/

/-- **The constructor tag of a load's payload, by the kind of the record**: a definition record's
by its kind, a projection record's by the kind of its member. -/
theorem rawCIRep_tag {E : Ixon.Env} {h : Heap F} {a : _root_.Address} {c : Ixon.Constant}
    {tag : String} {args : List (SourceValue F)}
    (raw : L1.RawCIRep E h a c (.construct "KernelTypes::KConstantInfo" tag args)) :
    match c.info with
    | .defn _ => tag = "Defn" ∨ tag = "Opaque" ∨ tag = "Thm"
    | .dPrj _ => tag = "Defn" ∨ tag = "Opaque" ∨ tag = "Thm"
    | .axio _ => tag = "Axiom"
    | .quot _ => tag = "Quot"
    | .recr _ => tag = "Rec"
    | .rPrj _ => tag = "Rec"
    | .iPrj _ => tag = "Induct"
    | .cPrj _ => tag = "Ctor"
    | .muts _ => False := by
  have hshape : ∀ (d : Ixon.Definition) (ty val hint : SourceValue F),
      Value.construct "KernelTypes::KConstantInfo" tag args = L1.defnValShape d ty val hint →
      tag = "Defn" ∨ tag = "Opaque" ∨ tag = "Thm" := by
    intro d ty val hint he
    unfold L1.defnValShape at he
    cases hk : d.kind <;> rw [hk] at he
    · exact Or.inl (Value.construct.inj he).2.1
    · exact Or.inr (Or.inl (Value.construct.inj he).2.1)
    · exact Or.inr (Or.inr (Value.construct.inj he).2.1)
  unfold L1.RawCIRep at raw
  cases hinfo : c.info with
  | defn d =>
    rw [hinfo] at raw
    obtain ⟨blobs, -, -, ty, val, hint, hv, -, -⟩ := raw
    exact hshape d ty val hint hv
  | dPrj p =>
    rw [hinfo] at raw
    obtain ⟨-, lcB, cb, ms, d, blobs, -, -, -, -, -, -, -, -, -, ty, val, hint, hv, -, -⟩ := raw
    exact hshape d ty val hint hv
  | axio ax =>
    rw [hinfo] at raw
    obtain ⟨blobs, -, -, ty, hv, -⟩ := raw
    exact (Value.construct.inj hv).2.1
  | quot q =>
    rw [hinfo] at raw
    obtain ⟨blobs, -, -, ty, hv, -⟩ := raw
    exact (Value.construct.inj hv).2.1
  | recr rc =>
    rw [hinfo] at raw
    obtain ⟨blobs, -, -, -, -, -, -, -, ty, rules, blk, b, -, -, hv, -, -⟩ := raw
    exact (Value.construct.inj hv).2.1
  | rPrj p =>
    rw [hinfo] at raw
    obtain ⟨-, lcB, cb, ms, rc, blobs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ty, rules, blk, b,
      -, -, hv, -, -⟩ := raw
    exact (Value.construct.inj hv).2.1
  | iPrj p =>
    rw [hinfo] at raw
    obtain ⟨-, lcB, cb, ms, ind, blobs, -, -, -, -, -, -, -, -, -, -, -, -, -, ty, blk, b,
      -, -, hv, -⟩ := raw
    exact (Value.construct.inj hv).2.1
  | cPrj p =>
    rw [hinfo] at raw
    obtain ⟨-, -, lcB, cb, ms, ind, ct, blobs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ty, blk,
      b, -, -, hv, -⟩ := raw
    exact (Value.construct.inj hv).2.1
  | muts ms =>
    rw [hinfo] at raw
    exact raw

/-! ## A constructor's owner -/

/-- **`CtorOfAnswers` of a run**: among the calls of a bounded run with its store, a load that
returns a constructor is the store's constructor projection record at the address, with the
constructor's counts of its block, and a load that returns another constant is a record of another
kind. -/
theorem ctorOfAnswers_of_run (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀) (hbd : Bounded calls) :
    CtorOfAnswers calls (ReconView.ofStore t E₀) := by
  intro xa p ci h m cs a ha ev hsub hld
  obtain ⟨c, hrec, raw⟩ := Guard.get_ci_rawCIRep_runStore hS hH
    (Guard.loadParentsHeld_of_runStore hS hH) (RomBound.bounded_mono hbd hsub) hsub ha ev hld
  show (∀ xnl xty xblk xind xcidx xnp xnf xuns,
      ci = .construct "KernelTypes::KConstantInfo" "Ctor"
        [xnl, xty, xblk, xind, xcidx, xnp, xnf, xuns] →
      ∃ (d : CtorData) (ba : Bytes.Address),
        ctorOfAt E₀ (ixAddr a) = some (some d) ∧
        d.nl < 4294967296 ∧ d.ind < 72057594037927936 ∧ d.np < 72057594037927936 ∧
        d.nf < 72057594037927936 ∧
        xnl = .field (d.nl : F) ∧ ixAddr ba = d.blk ∧ Bytes.RepAddressRef addrTy m ba xblk ∧
        xind = .field (d.ind : F) ∧ xnp = .field (d.np : F) ∧ xnf = .field (d.nf : F)) ∧
    ((∀ vs : List (SourceValue F), vs.length = 8 →
        ci ≠ .construct "KernelTypes::KConstantInfo" "Ctor" vs) →
      ctorOfAt E₀ (ixAddr a) = some none)
  by_cases hcp : ∃ cp, c.info = .cPrj cp
  · obtain ⟨cp, hinfo⟩ := hcp
    have raw' := raw
    unfold L1.RawCIRep at raw'
    rw [hinfo] at raw'
    obtain ⟨hidx, hcidx, lcB, cb, ms, ind, ct, blobs, -, -, hrecB, -, -, hms, hm, hct, -, hraw⟩ :=
      raw'
    obtain ⟨hl, -, hnp, hnf, hii, tyPtr, blkPtr, b, hbaddr, hbrep, hv, -⟩ := hraw
    have hmem : ms[cp.idx.toNat]? = some (.indc ind) := by
      rw [← Array.getElem?_toList]; exact hm
    have hctm : ind.ctors[cp.cidx.toNat]? = some ct := by
      rw [← Array.getElem?_toList]; exact hct
    have hctor : ctorOfAt E₀ (ixAddr a) = some (some ⟨ct.lvls.toNat, cp.block, cp.idx.toNat,
        ct.params.toNat, ct.fields.toNat⟩) := by
      unfold ctorOfAt
      simp only [hrec, hinfo, hS.recordOf_of_recordAt hrecB, hms, hmem, hctm]
    constructor
    · intro xnl xty xblk xind xcidx xnp xnf xuns hci
      rw [hci] at hv
      have hargs := (Value.construct.inj hv).2.2
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨e1, -, e3, e4, -, e6, e7, -⟩ := hargs
      exact ⟨_, b, hctor, hl, hii, hnp, hnf, e1, hbaddr, e3 ▸ hbrep, e4, e6, e7⟩
    · intro hne
      exact absurd hv (hne _ rfl)
  · constructor
    · intro xnl xty xblk xind xcidx xnp xnf xuns hci
      rw [hci] at raw
      have htag := rawCIRep_tag raw
      cases hinfo : c.info with
      | cPrj cp => exact absurd ⟨cp, hinfo⟩ hcp
      | defn d => rw [hinfo] at htag; simp at htag
      | dPrj _ => rw [hinfo] at htag; simp at htag
      | axio _ => rw [hinfo] at htag; simp at htag
      | quot _ => rw [hinfo] at htag; simp at htag
      | recr _ => rw [hinfo] at htag; simp at htag
      | rPrj _ => rw [hinfo] at htag; simp at htag
      | iPrj _ => rw [hinfo] at htag; simp at htag
      | muts _ => rw [hinfo] at htag; exact htag.elim
    · intro _
      unfold ctorOfAt
      rw [hrec]
      cases hinfo : c.info with
      | cPrj cp => exact absurd ⟨cp, hinfo⟩ hcp
      | _ => simp only [hinfo]

/-! ## A converted root is the model's loaded form, exactly and open -/

/-- **A converted root represents, exactly and as an open term, the model's loaded form of the
expression** (`FamilyFlat.loadedAt`): the root was converted from the record `src` with the
`recur` table `recurAddrs`, each of whose addresses `self` reads as its key, in the tree of the
record's binder blocks with the plan `plan` on the heap; the literal bytes the conversion hashed
are the reading's blobs; and the reading mentions only the level parameters below `n`. No scoping
of bound variables is asked: the term is represented at the local depth of its reading's bound. -/
theorem loadedAt_tmOExact (ht : t.check = .ok ())
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {recurAddrs : List _root_.Address} {n : Nat}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {e : Ixon.Expr}
    {kp : SourceValue F} {root : F} {tree : L1.BinderTreeData} {plan : List Core.KLevel}
    (hn : n < 4294967296)
    (hselfk : ∀ i x m k, recurAddrs[i]? = some x → self i = some m → m = .ok k →
      k = Core.keyOf t x)
    (hselfok : ∀ i x, recurAddrs[i]? = some x → ∃ m k, self i = some m ∧ m = .ok k)
    (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs)
    (raw : L1.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h 4294967295 e kp)
    (built : L1.BinderTreeBuilt (L1.binderLeavesData src.binders.toList) tree)
    (planned : L1.binderRootPlan tree src.sharing.toList root e = some plan)
    (levels : L1.HeapBinderLevels h kp plan)
    (hdef : ∀ v, (exprReader t blob src id self).read e = .ok v →
      v.allLevelParamsDefined (List.range n) = true) :
    ∃ E' : KExpr, loadedAt t blob src self n root e = some E' ∧ TmOExact (keyOf t) h E' kp := by
  obtain ⟨v, hread⟩ := LoadedReads.exprReader_read_ok (t := t) (blob := blob) (param := id)
    (self := self) ht raw hselfok hblob
  have hd := hdef v hread
  have hlbb : v.looseBVarsBounded v.bvarBound = true :=
    Ix.Kernel.Expr.looseBVarsBounded_iff.mpr (Nat.le_refl _)
  have hread' : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t blob) src
      (Ix.Kernel.Reader.recParam (List.range n)) self).read e = .ok v := by
    have h1 : (exprReader t blob src (Ix.Kernel.Reader.recParam (List.range n)) self).read e =
        .ok v := by
      rw [Assembly.recParam_range]
      exact hread
    exact h1
  obtain ⟨hecx, htbl⟩ := L1.memberReader_mk'_eq (readCtx t blob) src
    (Ix.Kernel.Reader.recParam (List.range n)) self
  unfold Ix.Kernel.Reader.MemberReader.read at hread'
  rw [hecx, htbl, ← List.take_length (l := src.sharing.toList)] at hread'
  obtain ⟨E', hann, htm, htrace⟩ :=
    raw.toTmExactTrace_of_blobAgreement (κ := Core.keyOf t) (ps := List.range n) (by simp)
      (by simpa using hn) rfl (by simp) (LoadedReads.readCtx_keyAt_inv ht blob) hselfk
      (L1.BlobReadAgreement.of_mem hblob) (Nat.le_refl _) (Nat.min_le_right _ _) hread' hlbb hd
  have hap := htrace plan levels []
  rw [List.append_nil] at hap
  refine ⟨E', ?_, v.bvarBound, ?_⟩
  · unfold loadedAt
    rw [hread]
    show LoadedReads.canonAnn src (List.range n) root e v = some E'
    unfold LoadedReads.canonAnn
    rw [LoadedReads.canonTree_eq built, planned]
    show (L1.applyBinderTrace (fun level => Core.bmeta (L1.invPosLevel (List.range n) level))
      v plan).map Prod.fst = some E'
    rw [hap]
    rfl
  · have hrep := htm 0 ghost0
    rwa [Decl.posOf_range] at hrep

/-! ## Level parameters of the readings -/

/-- **The readings at the address `a` mention only their constant's level parameters**: the value
of a definition (a standalone record's, or a block member's through its projection record) and
the type of an inductive member, read over the store's blobs: each mentions no level parameter
at or above its constant's level count. -/
structure LevelsDefinedAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (a : _root_.Address) :
    Prop where
  solo : ∀ (c : Ixon.Constant) (d : Ixon.Definition) (v : KExpr),
    recordOf E a = some c → c.info = .defn d → d.kind = .defn →
    (exprReader t (fun x => E.blobs.get? x) c id (soloSelf t a)).read d.value = .ok v →
    v.allLevelParamsDefined (List.range d.lvls.toNat) = true
  member : ∀ (c : Ixon.Constant) (p : Ixon.DefinitionProj) (cb : Ixon.Constant)
      (ms : Array Ixon.MutConst) (d : Ixon.Definition) (v : KExpr),
    recordOf E a = some c → c.info = .dPrj p → recordOf E p.block = some cb →
    cb.info = .muts ms → ms[p.idx.toNat]? = some (.defn d) → d.kind = .defn →
    (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t p.block ms)).read d.value =
      .ok v →
    v.allLevelParamsDefined (List.range d.lvls.toNat) = true
  ind : ∀ (c : Ixon.Constant) (p : Ixon.InductiveProj) (cb : Ixon.Constant)
      (ms : Array Ixon.MutConst) (ind : Ixon.Inductive) (v : KExpr),
    recordOf E a = some c → c.info = .iPrj p → recordOf E p.block = some cb →
    cb.info = .muts ms → ms[p.idx.toNat]? = some (.indc ind) →
    (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t p.block ms)).read ind.typ =
      .ok v →
    v.allLevelParamsDefined (List.range ind.lvls.toNat) = true

/-- **The readings at every address the calls `calls` load mention only their constant's level
parameters**: `LevelsDefinedAt` at the address of each `Ingress::get_ci` among `calls`. -/
def LoadedLevelsDefined (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (calls : List (Call F)) :
    Prop :=
  ∀ {xa : SourceValue F} {h : Heap F} {a : Bytes.Address},
    (⟨"Ingress::get_ci", [xa], h⟩ : Call F) ∈ calls → Bytes.RepAddressRef addrTy h a xa →
    LevelsDefinedAt t E (ixAddr a)

/-- Readings that mention only their level parameters at every address do so at the loaded
ones. -/
theorem loadedLevelsDefined_of_forall {E : Ixon.Env} (hlv : ∀ a, LevelsDefinedAt t E a) :
    LoadedLevelsDefined t E calls :=
  fun _ _ => hlv _

/-- Readings that mention only their level parameters at the addresses a run loads do so at
those any part of the run loads. -/
theorem LoadedLevelsDefined.mono {E : Ixon.Env} {cs : List (Call F)}
    (hlv : LoadedLevelsDefined t E calls) (hsub : ∀ c ∈ cs, c ∈ calls) :
    LoadedLevelsDefined t E cs :=
  fun hm ha => hlv (hsub _ hm) ha

/-! ## A definition's value -/

/-- **A converted definition against the model's loaded value**: a definition kind's payload is
`Defn` with its level count and a value pointer that represents, exactly and open, the loaded
form of the value at the root after the type's; another kind's payload is no `Defn`. -/
theorem defnTrace_answer (ht : t.check = .ok ())
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {tree : L1.BinderTreeData} {root : F} {m : Heap F} {d : Ixon.Definition}
    {ci : SourceValue F}
    (hselfk : ∀ i x mm k, recurAddrs[i]? = some x → self i = some mm → mm = .ok k →
      k = Core.keyOf t x)
    (hselfok : ∀ i x, recurAddrs[i]? = some x → ∃ mm k, self i = some mm ∧ mm = .ok k)
    (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs)
    (built : L1.BinderTreeBuilt (L1.binderLeavesData src.binders.toList) tree)
    (rep : L1.DefnTraceRep src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      tree root m d ci)
    (hdef : d.kind = .defn → ∀ v, (exprReader t blob src id self).read d.value = .ok v →
      v.allLevelParamsDefined (List.range d.lvls.toNat) = true) :
    d.lvls.toNat < 4294967296 ∧
    (d.kind = .defn → ∃ (xty xval xsf xh : SourceValue F) (E' : KExpr),
      ci = .construct "KernelTypes::KConstantInfo" "Defn"
        [.field (d.lvls.toNat : F), xty, xval, xsf, xh] ∧
      loadedAt t blob src self d.lvls.toNat (root + 1) d.value = some E' ∧
      TmOExact (keyOf t) m E' xval) ∧
    (d.kind ≠ .defn → ∀ vs : List (SourceValue F),
      ci ≠ .construct "KernelTypes::KConstantInfo" "Defn" vs) := by
  obtain ⟨hnl, tyPtr, valPtr, hint, planT, planV, hv, rty, rval, hpT, hpV, hlT, hlV⟩ := rep
  refine ⟨hnl, ?_, ?_⟩
  · intro hk
    obtain ⟨E', hl, htm⟩ := loadedAt_tmOExact ht hnl hselfk hselfok hblob rval built hpV hlV
      (hdef hk)
    refine ⟨tyPtr, valPtr, L1.repDefSafetyVal d.safety, hint, E', ?_, hl, htm⟩
    rw [hv]
    unfold L1.defnValShape
    rw [hk]
  · intro hk vs hci
    rw [hci] at hv
    unfold L1.defnValShape at hv
    cases hkd : d.kind with
    | defn => exact hk hkd
    | opaq => rw [hkd] at hv; exact absurd (Value.construct.inj hv).2.1 (by decide)
    | thm => rw [hkd] at hv; exact absurd (Value.construct.inj hv).2.1 (by decide)

/-- **The `Defn` clauses from the store's definition at the address**: where the store reads a
definition (`defnAt`) whose level count and value the payload carries, or reads none and the
payload is no `Defn`. -/
theorem defn_clause_of_defnAt (hwf : t.wf = true) {E : Ixon.Env} {A : _root_.Address}
    {ci : SourceValue F} {m : Heap F} {X : Option (Nat × KExpr)}
    (hX : defnAt t E A = some X)
    (hsome : ∀ n v, X = some (n, v) → ∃ (xty xval xsf xh : SourceValue F),
      ci = .construct "KernelTypes::KConstantInfo" "Defn" [.field (n : F), xty, xval, xsf, xh] ∧
      n < 4294967296 ∧ TmOExact (keyOf t) m v xval)
    (hnone : X = none → ∀ vs : List (SourceValue F),
      ci ≠ .construct "KernelTypes::KConstantInfo" "Defn" vs) :
    (∀ xnl xty xval xsf xh,
      ci = .construct "KernelTypes::KConstantInfo" "Defn" [xnl, xty, xval, xsf, xh] →
      ∃ (nl : Nat) (val : KExpr),
        xnl = .field (nl : F) ∧ nl < 4294967296 ∧ TmOExact (keyOf t) m val xval ∧
        ∀ us, unfoldAt t E (keyOf t A) us =
          if us.length = nl then some (some (exprInstLevels us val)) else some none) ∧
    ((∀ vs : List (SourceValue F), vs.length = 5 →
        ci ≠ .construct "KernelTypes::KConstantInfo" "Defn" vs) →
      ∀ us, unfoldAt t E (keyOf t A) us = some none) := by
  cases X with
  | none =>
    refine ⟨fun xnl xty xval xsf xh hci => absurd hci (hnone rfl _), fun _ us => ?_⟩
    unfold unfoldAt
    rw [keyAddr_keyOf hwf]
    simp only [hX]
  | some nv =>
    obtain ⟨n, v⟩ := nv
    obtain ⟨xty', xval', xsf', xh', hci', hn, htm⟩ := hsome n v rfl
    refine ⟨fun xnl xty xval xsf xh hci => ?_, fun hne => absurd hci' (hne _ rfl)⟩
    rw [hci'] at hci
    have hargs := (Value.construct.inj hci).2.2
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨e1, -, e3, -, -⟩ := hargs
    refine ⟨n, v, e1.symm, hn, e3 ▸ htm, fun us => ?_⟩
    unfold unfoldAt
    rw [keyAddr_keyOf hwf]
    simp only [hX]

/-- **A load of a run against the store's definition at the address** (`defnAt`): among the
calls of a bounded run with its store, at an address whose readings mention only their level
parameters, the store reads a definition or none at the loaded address; where it reads a
definition, the load returned a `Defn` with its level count and a value pointer representing its
value exactly, as the open loaded form; where it reads none, the load returned no `Defn`. -/
theorem defnAt_of_load (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls)
    {xa p ci : SourceValue F} {h m : Heap F} {cs : List (Call F)} {a : Bytes.Address}
    (hlv : LevelsDefinedAt t E₀ (ixAddr a))
    (ha : Bytes.RepAddressRef addrTy h a xa)
    (ev : ObsFn W "Ingress::get_ci" [xa] h p m cs) (hsub : ∀ c ∈ cs, c ∈ calls)
    (hld : loadValue m p = .ok ci) :
    ∃ X : Option (Nat × KExpr), defnAt t E₀ (ixAddr a) = some X ∧
      (∀ n v, X = some (n, v) → ∃ (xty xval xsf xh : SourceValue F),
        ci = .construct "KernelTypes::KConstantInfo" "Defn"
          [.field (n : F), xty, xval, xsf, xh] ∧
        n < 4294967296 ∧ TmOExact (keyOf t) m v xval) ∧
      (X = none → ∀ vs : List (SourceValue F),
        ci ≠ .construct "KernelTypes::KConstantInfo" "Defn" vs) := by
  obtain ⟨c, hrec, raw⟩ := Guard.get_ci_rawCIRep_runStore hS hH
    (Guard.loadParentsHeld_of_runStore hS hH) (RomBound.bounded_mono hbd hsub) hsub ha ev hld
  obtain ⟨rawBytes, c', hh, haddr, hex, hres⟩ := L1.get_ci_trace_spec ha ev
  have hcc : c = c' := (hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hrec)
    (Core.hashed_mono hsub hh) haddr hex).symm
  subst hcc
  have hblob : ∀ {blobs : List (_root_.Address × ByteArray)}, L1.HashedPairs cs blobs →
      ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro blobs hhp x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hb := hS.blobs bs (Core.hashed_mono hsub hhx)
    have hxa' : Address.blake3Pure bs = x := hxa
    rw [hxa'] at hb
    exact hb
  -- a record of another kind
  have other : (∀ d, c.info ≠ .defn d) → (∀ dp, c.info ≠ .dPrj dp) →
      defnAt t E₀ (ixAddr a) = some none ∧
      ∀ vs : List (SourceValue F), ci ≠ .construct "KernelTypes::KConstantInfo" "Defn" vs := by
    intro h1 h2
    constructor
    · unfold defnAt
      rw [hrec]
      cases hinfo : c.info with
      | defn d => exact absurd hinfo (h1 d)
      | dPrj dp => exact absurd hinfo (h2 dp)
      | _ => simp only [hinfo]
    · intro vs hci
      rw [hci] at raw
      have htag := rawCIRep_tag raw
      cases hinfo : c.info with
      | defn d => exact absurd hinfo (h1 d)
      | dPrj dp => exact absurd hinfo (h2 dp)
      | axio _ => rw [hinfo] at htag; simp at htag
      | quot _ => rw [hinfo] at htag; simp at htag
      | recr _ => rw [hinfo] at htag; simp at htag
      | rPrj _ => rw [hinfo] at htag; simp at htag
      | iPrj _ => rw [hinfo] at htag; simp at htag
      | cPrj _ => rw [hinfo] at htag; simp at htag
      | muts _ => rw [hinfo] at htag; exact htag.elim
  unfold L1.GetCITraceResult at hres
  by_cases hd : ∃ d, c.info = .defn d
  · -- a standalone definition record
    obtain ⟨d, hinfo⟩ := hd
    rw [hinfo] at hres
    obtain ⟨blobs, tree, v, hhp, built, hld', rep⟩ := hres
    have hvci : v = ci := Except.ok.inj (hld'.symm.trans hld)
    subst hvci
    have hrecur : ∀ (i : Nat) (x : _root_.Address),
        (L1.defnRecurAddrs d (ixAddr a))[i]? = some x →
        ([ixAddr a] : List _root_.Address)[i]? = some x := by
      intro i x hx
      unfold L1.defnRecurAddrs at hx
      split at hx
      · exact hx
      · simp at hx
    obtain ⟨hnl, hyes, hno⟩ := defnTrace_answer (t := t)
      (blob := fun x => E₀.blobs.get? x) (self := soloSelf t (ixAddr a))
      (recurAddrs := L1.defnRecurAddrs d (ixAddr a)) ht
      (fun i x mm k hx => LoadedReads.soloSelf_key t (ixAddr a) i x mm k (hrecur i x hx))
      (fun i x hx => LoadedReads.soloSelf_ok t (ixAddr a) i x (hrecur i x hx))
      (hblob hhp) built rep
      (fun hk v hv => hlv.solo c d v hrec hinfo hk hv)
    by_cases hk : d.kind = .defn
    · obtain ⟨xty, xval, xsf, xh, E', hci, hl, htm⟩ := hyes hk
      rw [zero_add] at hl
      refine ⟨some (d.lvls.toNat, E'), ?_, ?_, fun hX => by cases hX⟩
      · unfold defnAt
        simp only [hrec, hinfo, hk, hl]
        rfl
      · intro n v hnv
        cases hnv
        exact ⟨xty, xval, xsf, xh, hci, hnl, htm⟩
    · refine ⟨none, ?_, (fun n v hX => by cases hX), (fun _ => hno hk)⟩
      unfold defnAt
      cases hkd : d.kind with
      | defn => exact absurd hkd hk
      | opaq => simp only [hrec, hinfo, hkd]
      | thm => simp only [hrec, hinfo, hkd]
  · by_cases hdp : ∃ dp, c.info = .dPrj dp
    · -- a definition member of a block
      obtain ⟨dp, hinfo⟩ := hdp
      rw [hinfo] at hres
      obtain ⟨hidx, blkBytes, cb, ms, d, blobs, tree, v, hhB, haddrB, hexB, hms, hm, hhp, built,
        hld', rep⟩ := hres
      have hvci : v = ci := Except.ok.inj (hld'.symm.trans hld)
      subst hvci
      have raw' := raw
      unfold L1.RawCIRep at raw'
      rw [hinfo] at raw'
      obtain ⟨-, lcB, cb₂, ms₂, d₂, blobs₂, -, -, hrecB, -, -, -, -, -, -⟩ := raw'
      have hcb : cb = cb₂ := hS.record_eq hrecB (Core.hashed_mono hsub hhB) haddrB hexB
      subst hcb
      have hrecB' : recordOf E₀ dp.block = some cb := hS.recordOf_of_recordAt hrecB
      have hmem : ms[dp.idx.toNat]? = some (.defn d) := by
        rw [← Array.getElem?_toList]; exact hm
      have hrecur : ∀ (i : Nat) (x : _root_.Address),
          (L1.defnMemberRecurAddrs d dp.block ms.toList)[i]? = some x →
          (L1.blockRecurAddrs dp.block ms.toList)[i]? = some x := by
        intro i x hx
        unfold L1.defnMemberRecurAddrs at hx
        split at hx
        · exact hx
        · simp at hx
      obtain ⟨hnl, hyes, hno⟩ := defnTrace_answer (t := t)
        (blob := fun x => E₀.blobs.get? x) (self := blockSelf t dp.block ms)
        (recurAddrs := L1.defnMemberRecurAddrs d dp.block ms.toList) ht
        (fun i x mm k hx => LoadedReads.blockSelf_key t dp.block ms i x mm k (hrecur i x hx))
        (fun i x hx => LoadedReads.blockSelf_ok t dp.block ms i x (hrecur i x hx))
        (hblob hhp) built rep
        (fun hk v hv => hlv.member c dp cb ms d v hrec hinfo hrecB' hms hmem hk hv)
      by_cases hk : d.kind = .defn
      · obtain ⟨xty, xval, xsf, xh, E', hci, hl, htm⟩ := hyes hk
        refine ⟨some (d.lvls.toNat, E'), ?_, ?_, fun hX => by cases hX⟩
        · unfold defnAt
          simp only [hrec, hinfo, hrecB', hms, hmem, hk, hl]
          rfl
        · intro n v hnv
          cases hnv
          exact ⟨xty, xval, xsf, xh, hci, hnl, htm⟩
      · refine ⟨none, ?_, (fun n v hX => by cases hX), (fun _ => hno hk)⟩
        unfold defnAt
        cases hkd : d.kind with
        | defn => exact absurd hkd hk
        | opaq => simp only [hrec, hinfo, hrecB', hms, hmem, hkd]
        | thm => simp only [hrec, hinfo, hrecB', hms, hmem, hkd]
    · obtain ⟨hX, hno⟩ := other (fun d hi => hd ⟨d, hi⟩) (fun dp hi => hdp ⟨dp, hi⟩)
      exact ⟨none, hX, (fun n v hX' => by cases hX'), (fun _ => hno)⟩

/-- **`DefnAnswers` of a run**: among the calls of a bounded run with its store, the readings at
whose loaded addresses mention only their level parameters, a load that returns a definition is
the store's definition at the address, its value represented exactly as the open loaded form the
model unfolds to; a load that returns another constant is no definition of the store. -/
theorem defnAnswers_of_run (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls) (hlv : LoadedLevelsDefined t E₀ calls) :
    DefnAnswers calls (keyOf t) (ReconView.ofStore t E₀) := by
  intro xa p ci h m cs a ha ev hself hsub hld
  obtain ⟨X, hX, hsome, hnone⟩ := defnAt_of_load ht hS hH hbd (hlv hself ha) ha ev hsub hld
  exact defn_clause_of_defnAt hwf hX hsome hnone

/-! ## An inductive's data -/

/-- **A load of a run against the store's inductive at the address** (`indDataAt`): among the
calls of a bounded run with its store, at an address whose readings mention only their level
parameters, a load that returns an `Induct` is the store's inductive at the address: its counts,
block and position, with the type pointer representing its type exactly, as the open loaded
form; a load that returns another constant is a record of another kind. -/
theorem indDataAt_of_load (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls)
    {xa p ci : SourceValue F} {h m : Heap F} {cs : List (Call F)} {a : Bytes.Address}
    (hlv : LevelsDefinedAt t E₀ (ixAddr a))
    (ha : Bytes.RepAddressRef addrTy h a xa)
    (ev : ObsFn W "Ingress::get_ci" [xa] h p m cs) (hsub : ∀ c ∈ cs, c ∈ calls)
    (hld : loadValue m p = .ok ci) :
    (∀ xnl xty xnp xni xnc xrec xblk xidx,
      ci = .construct "KernelTypes::KConstantInfo" "Induct"
        [xnl, xty, xnp, xni, xnc, xrec, xblk, xidx] →
      ∃ (d : IndData) (ba : Bytes.Address),
        indDataAt t E₀ (ixAddr a) = some (some d) ∧
        d.nl < 4294967296 ∧ d.np < 72057594037927936 ∧ d.ni < 72057594037927936 ∧
        d.nctors < 72057594037927936 ∧ d.idx < 72057594037927936 ∧
        xnl = .field (d.nl : F) ∧ TmOExact (keyOf t) m d.ty xty ∧
        xnp = .field (d.np : F) ∧ xni = .field (d.ni : F) ∧ xnc = .field (d.nctors : F) ∧
        ixAddr ba = d.blk ∧ Bytes.RepAddressRef addrTy m ba xblk ∧ xidx = .field (d.idx : F)) ∧
    ((∀ vs : List (SourceValue F), vs.length = 8 →
        ci ≠ .construct "KernelTypes::KConstantInfo" "Induct" vs) →
      indDataAt t E₀ (ixAddr a) = some none) := by
  obtain ⟨c, hrec, raw⟩ := Guard.get_ci_rawCIRep_runStore hS hH
    (Guard.loadParentsHeld_of_runStore hS hH) (RomBound.bounded_mono hbd hsub) hsub ha ev hld
  by_cases hip : ∃ ip, c.info = .iPrj ip
  · obtain ⟨ip, hinfo⟩ := hip
    obtain ⟨rawBytes, c', hh, haddr, hex, -, hres⟩ :=
      L1.get_ci_block_trace_spec (RomBound.bounded_mono hbd hsub) ha ev
    have hcc : c = c' := (hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hrec)
      (Core.hashed_mono hsub hh) haddr hex).symm
    subst hcc
    unfold L1.GetCIBlockTraceResult at hres
    rw [hinfo] at hres
    obtain ⟨hidx, blkBytes, cb, ms, ind, blobs, tree, plan, v, hhB, haB, hexB, hcb, hm, hhp,
      built, planned, hld', hraw, hlev⟩ := hres
    have hvci : v = ci := Except.ok.inj (hld'.symm.trans hld)
    subst hvci
    have raw' := raw
    unfold L1.RawCIRep at raw'
    rw [hinfo] at raw'
    obtain ⟨-, lcB, cb₂, ms₂, ind₂, blobs₂, -, -, hrecB, -, -, -, -, -, -⟩ := raw'
    have hcbe : cb = cb₂ := hS.record_eq hrecB (Core.hashed_mono hsub hhB) haB hexB
    subst hcbe
    have hrecB' : recordOf E₀ ip.block = some cb := hS.recordOf_of_recordAt hrecB
    have hmem : ms[ip.idx.toNat]? = some (.indc ind) := by
      rw [← Array.getElem?_toList]; exact hm
    obtain ⟨hl, hnp, hni, hnc, hii, tyPtr, blkPtr, b, hbaddr, hbrep, hv, rty⟩ := hraw
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
      have hb := hS.blobs bs (Core.hashed_mono hsub hhx)
      have hxa' : Address.blake3Pure bs = x := hxa
      rw [hxa'] at hb
      exact hb
    obtain ⟨ty, hlt, htm⟩ := loadedAt_tmOExact (t := t) (blob := fun x => E₀.blobs.get? x)
      (self := blockSelf t ip.block ms) (recurAddrs := L1.blockRecurAddrs ip.block ms.toList)
      ht hl (LoadedReads.blockSelf_key t ip.block ms) (LoadedReads.blockSelf_ok t ip.block ms)
      hblob rty built planned trace
      (fun v hv' => hlv.ind c ip cb ms ind v hrec hinfo hrecB' hcb hmem hv')
    have hdata : indDataAt t E₀ (ixAddr a) = some (some ⟨ind.lvls.toNat, ty, ind.params.toNat,
        ind.indices.toNat, ind.ctors.size, ip.block, ip.idx.toNat⟩) := by
      unfold indDataAt
      simp only [hrec, hinfo, hrecB', hcb, hmem, hlt]
    constructor
    · intro xnl xty xnp xni xnc xrec xblk xidx hci
      rw [hci] at hv
      have hargs := (Value.construct.inj hv).2.2
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨e1, e2, e3, e4, e5, -, e7, e8⟩ := hargs
      exact ⟨_, b, hdata, hl, hnp, hni, hnc, hii, e1, e2 ▸ htm, e3, e4, e5, hbaddr,
        e7 ▸ hbrep, e8⟩
    · intro hne
      exact absurd hv (hne _ rfl)
  · constructor
    · intro xnl xty xnp xni xnc xrec xblk xidx hci
      rw [hci] at raw
      have htag := rawCIRep_tag raw
      cases hinfo : c.info with
      | iPrj ip => exact absurd ⟨ip, hinfo⟩ hip
      | defn d => rw [hinfo] at htag; simp at htag
      | dPrj _ => rw [hinfo] at htag; simp at htag
      | axio _ => rw [hinfo] at htag; simp at htag
      | quot _ => rw [hinfo] at htag; simp at htag
      | recr _ => rw [hinfo] at htag; simp at htag
      | rPrj _ => rw [hinfo] at htag; simp at htag
      | cPrj _ => rw [hinfo] at htag; simp at htag
      | muts _ => rw [hinfo] at htag; exact htag.elim
    · intro _
      unfold indDataAt
      rw [hrec]
      cases hinfo : c.info with
      | iPrj ip => exact absurd ⟨ip, hinfo⟩ hip
      | _ => simp only [hinfo]

/-- **`IndAnswers` of a run**: among the calls of a bounded run with its store, the readings at
whose loaded addresses mention only their level parameters, a load that returns an inductive is
the store's inductive at the address, its type represented exactly as the open loaded form; a
load that returns another constant is a record of another kind. -/
theorem indAnswers_of_run (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls) (hlv : LoadedLevelsDefined t E₀ calls) :
    IndAnswers calls (keyOf t) (ReconView.ofStore t E₀) := by
  intro xa p ci h m cs a ha ev hself hsub hld
  exact indDataAt_of_load ht hS hH hbd (hlv hself ha) ha ev hsub hld

/-! ## The five together -/

/-- **The reconstruction's store answers of a run**: for a bounded run with its store, at a
well-formed table, the view of the store inverts the keying, and among the run's calls a load or
a dispatch answers the view: a definition and an inductive where the readings at the addresses
the run loads mention only their level parameters, a constructor and the modeled-route test
outright; the dispatch where the run hashes no collision with its store. -/
theorem storeAnswers_of_run (ht : t.check = .ok ()) (hwf : t.wf = true)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls) (hnc : ¬ View.HashedCollision { env := E₀ } [] calls)
    (hlv : LoadedLevelsDefined t E₀ calls) :
    AddrOf (keyOf t) (ReconView.ofStore t E₀) ∧
    DefnAnswers calls (keyOf t) (ReconView.ofStore t E₀) ∧
    IndAnswers calls (keyOf t) (ReconView.ofStore t E₀) ∧
    CtorOfAnswers calls (ReconView.ofStore t E₀) ∧
    ModeledAnswers calls (ReconView.ofStore t E₀) :=
  ⟨addrOf_ofStore hwf E₀, defnAnswers_of_run ht hwf hS hH hbd hlv,
    indAnswers_of_run ht hS hH hbd hlv, ctorOfAnswers_of_run hS hH hbd,
    modeledAnswers_of_run hH hbd hnc⟩

/-- **A run that hashes no collision with a view hashes none with its store**: every byte string
the store holds is one the run hashed under its address (the records and blobs by `LoadedBy`, the
role binding's bytes by assumption), so a collision with the store is one among what the run
hashed. -/
theorem storeNoCollision_of_view {V : View} {extra : List ByteArray}
    (hload : LoadedBy calls E₀)
    (hrb : ∀ rb, E₀.roleBinding = some rb →
      Hashed calls rb.bytes ∧ Address.blake3Pure rb.bytes = rb.address)
    (hno : ¬ V.HashedCollision extra calls) :
    ¬ View.HashedCollision { env := E₀ } [] calls := by
  have hpre : ∀ {x : _root_.Address} {held : ByteArray},
      ({ env := E₀ } : View).Preimage x held →
      Hashed calls held ∧ Address.blake3Pure held = x := by
    intro x held hp
    rcases hp with ⟨lc, hget, rfl⟩ | hblob | ⟨rb, hr, rfl, rfl⟩ | ⟨tr, htr, -, -⟩
    · exact hload.1 x lc hget
    · exact hload.2 x held hblob
    · exact hrb rb hr
    · cases htr
  have hanchor : ∀ {x : _root_.Address} {held : ByteArray},
      (({ env := E₀ } : View).Preimage x held ∨
        (held ∈ ([] : List ByteArray) ∧ Address.blake3Pure held = x) ∨
        (Hashed calls held ∧ Address.blake3Pure held = x)) →
      Hashed calls held ∧ Address.blake3Pure held = x := by
    intro x held hsrc
    rcases hsrc with hp | ⟨hm, -⟩ | hh
    · exact hpre hp
    · cases hm
    · exact hh
  intro hcol
  apply hno
  rcases hcol with ⟨x, held, bytes, hsrc, hh, hne, hblk⟩ |
    ⟨x, held, image, blk, cb, ms, hsrc, hb, hdec, hms, himg, hne, hblk⟩ | ⟨bytes, hsrc, hpad⟩
  · exact Or.inl ⟨x, held, bytes, Or.inr (Or.inr (hanchor hsrc)), hh, hne, hblk⟩
  · exact Or.inr (Or.inl ⟨x, held, image, blk, cb, ms, Or.inr (Or.inr (hanchor hsrc)), hb, hdec,
      hms, himg, hne, hblk⟩)
  · refine Or.inr (Or.inr ⟨bytes, Or.inr ?_, hpad⟩)
    rcases hsrc with hp | hh
    · exact (hpre hp).1
    · exact hh

/-! ## The loads as lookups of the store -/

/-- A definition in the reconstruction's reading is the flattening's lookup of it. -/
theorem defnValAt_of_defnAt {E : Ixon.Env} {a : _root_.Address} {n : Nat} {v : KExpr}
    (h : defnAt t E a = some (some (n, v))) : FamilyFlat.defnValAt t E a = some (n, v) := by
  unfold defnAt at h
  unfold FamilyFlat.defnValAt
  repeat' split at h
  all_goals simp_all
  all_goals (obtain ⟨h, rfl⟩ := h; exact h)

end Run

end IxVM.Refinement.Binding.FamilyRecon
