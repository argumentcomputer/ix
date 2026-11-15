import IxVMRefinement.L1.Records
import IxVMRefinement.Core.RawRecords

/-! # Raw query facts from canonical decoded records

Each selected query carries its observed invocation and canonical input record. If that
record is an inductive projection, its parent is also retained. Collision freedom then makes
any successful reading at that exact input agree with these records, independently of the
semantic environment's installed constants.
-/

namespace IxVM.Refinement.L1

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core (ScopedCtx Ctx RawRecordFacts)

/-- A particular stored record together with its canonical decoding. -/
structure CanonicalRecordAt (E : Ixon.Env) (a : _root_.Address) where
  entry : Ixon.LazyConstant
  value : Ixon.Constant
  stored : E.consts.get? a = some entry
  cached : entry.get? = some value
  decoded : Ixon.deConstantExact entry.rawBytes = .ok value

theorem CanonicalRecordAt.recordAt {E : Ixon.Env} {a : _root_.Address}
    (r : CanonicalRecordAt E a) : Ix.Cert.recordAt E a = some r.value := by
  unfold Ix.Cert.recordAt
  rw [r.stored]
  exact r.cached

theorem CanonicalRecordAt.ofStoredCanonical {E : Ixon.Env} {order : List _root_.Address}
    {a : _root_.Address} {value : Ixon.Constant}
    (canonical : Ix.Cert.Stream.StoredCanonical E order) (member : a ∈ order)
    (record : Ix.Cert.recordAt E a = some value) : Nonempty (CanonicalRecordAt E a) := by
  unfold Ix.Cert.recordAt at record
  cases stored : E.consts.get? a with
  | none => rw [stored] at record; cases record
  | some entry =>
    rw [stored] at record
    exact ⟨⟨entry, value, stored, record,
      deConstantExact_of_storedCanonical canonical member stored record⟩⟩

/-- One actual raw record invocation, with only its decoded-record coverage. -/
structure RawRecordQuery (E : Ixon.Env) where
  addr : SourceValue F
  result : SourceValue F
  before : Heap F
  after : Heap F
  calls : List (Call F)
  address : Bytes.Address
  observed : ObsFn Core.W "Ingress::get_ci" [addr] before result after calls
  addressRep : Bytes.RepAddressRef Core.addrTy before address addr
  source : CanonicalRecordAt E (Core.ixAddr address)
  parents : ∀ p, source.value.info = .iPrj p → Nonempty (CanonicalRecordAt E p.block)

def RawRecordQuery.top {E : Ixon.Env} (q : RawRecordQuery E) : Call F :=
  ⟨"Ingress::get_ci", [q.addr], q.before⟩

/-- The scope consists of the exact top invocations selected by the supplied observations. -/
def rawQueryCtx (base : Ctx) (queries : List (RawRecordQuery base.E)) : ScopedCtx :=
  { toCtx := base, allowed := fun call => ∃ q ∈ queries, call = q.top }

theorem RawRecordQuery.allowed {base : Ctx} {queries : List (RawRecordQuery base.E)}
    {q : RawRecordQuery base.E} (member : q ∈ queries) :
    (rawQueryCtx base queries).allowedTop "Ingress::get_ci" [q.addr] q.before :=
  ⟨q, member, rfl⟩

/-- L1 constructs the raw record and parent identities for a selected canonical query.
The queried constant need not be installed in the semantic environment. -/
theorem RawRecordQuery.inductiveRead {base : Ctx} (q : RawRecordQuery base.E)
    {ptr : SourceValue F} {h' : Heap F} {calls : List (Call F)}
    {nl ty np ni nc u blk idx : SourceValue F}
    (observed : ObsFn Core.W "Ingress::get_ci" [q.addr] q.before ptr h' calls)
    (good : Core.Good base calls)
    (loaded : loadValue h' ptr =
      .ok (.construct Core.kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx])) :
    ∃ (cm cb : Ixon.Constant) (xs : Array Ixon.MutConst) (ind : Ixon.Inductive)
      (b : Bytes.Address) (i : F),
      Ix.Cert.recordAt base.E (Core.ixAddr q.address) = some cm ∧
      Bytes.RepAddressRef Core.addrTy h' b blk ∧ idx = .field i ∧
      cm.info = .iPrj ⟨(ZMod.val i).toUInt64, Core.ixAddr b⟩ ∧
      Ix.Cert.recordAt base.E (Core.ixAddr b) = some cb ∧ cb.info = .muts xs ∧
      xs[ZMod.val i]? = some (.indc ind) := by
  obtain ⟨bytes, blockBytes, cm, cb, xs, ind, b, i, hh, ha, decoded, _,
    hhb, hab, decodedBlock, _, hb, hi, _, hp, hcb, hind⟩ :=
    inductRecord_raw_of_get_ci observed good.2 q.addressRep loaded
  have bytesEq := Core.load_escape q.source.stored good.1 bytes hh ha
  rw [bytesEq, q.source.decoded] at decoded
  injection decoded with hcm
  subst cm
  obtain ⟨parent⟩ := q.parents _ hp
  have blockEq := Core.load_escape parent.stored good.1 blockBytes hhb hab
  rw [blockEq, parent.decoded] at decodedBlock
  injection decodedBlock with hparent
  subst cb
  exact ⟨q.source.value, parent.value, xs, ind, b, i,
    q.source.recordAt, hb, hi, hp, parent.recordAt, hcb, hind⟩

/-- A list of actual canonical raw queries produces the metadata contract for exactly
those invocations. This constructs no installed semantic lookup facts. -/
theorem rawRecordFacts_of_queries (base : Ctx) (queries : List (RawRecordQuery base.E)) :
    RawRecordFacts (rawQueryCtx base queries) where
  inductiveRead := by
    intro addr ptr h h' cs a nl ty np ni nc u blk idx observed allowed good ha loaded
    obtain ⟨q, _, same⟩ := allowed
    have heapEq : h = q.before := congrArg Call.heap same
    have argsEq : [addr] = [q.addr] := congrArg Call.args same
    have addrEq : addr = q.addr := (List.cons.inj argsEq).1
    subst h addr
    have addressEq : a = q.address :=
      Bytes.repAddressRef_inj U32.Goldilocks.compatible ha q.addressRep
    subst a
    exact q.inductiveRead observed good loaded

/-- An observed query of a known inductive projection and its canonical parent constructs
a nonempty selected-query scope, even when both semantic names are still fresh. -/
theorem rawRecordFacts_singleton {base : Ctx} {order : List _root_.Address}
    {addr ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {a : Bytes.Address}
    {cm cb : Ixon.Constant} {p : Ixon.InductiveProj}
    (observed : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs)
    (addressRep : Bytes.RepAddressRef Core.addrTy h a addr)
    (canonical : Ix.Cert.Stream.StoredCanonical base.E order)
    (member : Core.ixAddr a ∈ order) (parentMember : p.block ∈ order)
    (record : Ix.Cert.recordAt base.E (Core.ixAddr a) = some cm)
    (projection : cm.info = .iPrj p) (parent : Ix.Cert.recordAt base.E p.block = some cb) :
    ∃ q : RawRecordQuery base.E, q.top = ⟨"Ingress::get_ci", [addr], h⟩ ∧
      RawRecordFacts (rawQueryCtx base [q]) := by
  obtain ⟨source⟩ := CanonicalRecordAt.ofStoredCanonical canonical member record
  obtain ⟨parent⟩ := CanonicalRecordAt.ofStoredCanonical canonical parentMember parent
  have sourceEq : source.value = cm := Option.some.inj (source.recordAt.symm.trans record)
  let q : RawRecordQuery base.E :=
    { addr, result := ptr, before := h, after := h', calls := cs, address := a
      observed, addressRep, source
      parents := by
        intro p' hp'
        rw [sourceEq, projection] at hp'
        cases Ixon.ConstantInfo.iPrj.inj hp'
        exact ⟨parent⟩ }
  exact ⟨q, rfl, rawRecordFacts_of_queries base [q]⟩

/-- Decoded coverage of the raw queries in one actual trace. This mentions only input heaps,
source records, and their serialized projection parents. -/
def CanonicalQueryCoverage (E : Ixon.Env) (calls : List (Call F)) : Prop :=
  ∀ addr heap, (⟨"Ingress::get_ci", [addr], heap⟩ : Call F) ∈ calls →
    ∃ (a : Bytes.Address) (source : CanonicalRecordAt E (Core.ixAddr a)),
      Bytes.RepAddressRef Core.addrTy heap a addr ∧
      ∀ p, source.value.info = .iPrj p → Nonempty (CanonicalRecordAt E p.block)

private theorem queryList_of_cover (base : Ctx) :
    ∀ calls : List (Call F),
      (∀ addr heap, (⟨"Ingress::get_ci", [addr], heap⟩ : Call F) ∈ calls →
        ∃ q : RawRecordQuery base.E, q.top = ⟨"Ingress::get_ci", [addr], heap⟩) →
      ∃ queries : List (RawRecordQuery base.E),
        Core.RawRecordCoverage (rawQueryCtx base queries) calls
  | [], _ => ⟨[], fun _ _ member => nomatch member⟩
  | call :: calls, covered => by
    classical
    obtain ⟨queries, rest⟩ := queryList_of_cover base calls
      (fun addr heap member => covered addr heap (List.mem_cons_of_mem call member))
    by_cases isQuery : ∃ addr heap, call = (⟨"Ingress::get_ci", [addr], heap⟩ : Call F)
    · obtain ⟨addr₀, heap₀, rfl⟩ := isQuery
      obtain ⟨q, same⟩ := covered addr₀ heap₀ List.mem_cons_self
      refine ⟨q :: queries, fun addr heap member => ?_⟩
      rcases List.mem_cons.mp member with equal | member
      · exact ⟨q, List.mem_cons_self, equal.trans same.symm⟩
      · obtain ⟨q', hq', same'⟩ := rest addr heap member
        exact ⟨q', List.mem_cons_of_mem q hq', same'⟩
    · refine ⟨queries, fun addr heap member => ?_⟩
      rcases List.mem_cons.mp member with equal | member
      · exact False.elim (isQuery ⟨addr, heap, equal.symm⟩)
      · exact rest addr heap member

/-- Recover all selected raw queries from their actual sub-observations, then construct both
the raw record facts and coverage of this trace's raw invocations. -/
theorem rawRecordFacts_of_trace {base : Ctx} {name : String} {args : List (SourceValue F)}
    {h h' : Heap F} {result : SourceValue F} {calls : List (Call F)}
    (observed : ObsFn Core.W name args h result h' calls)
    (known : CanonicalQueryCoverage base.E calls) :
    ∃ queries : List (RawRecordQuery base.E),
      RawRecordFacts (rawQueryCtx base queries) ∧
      Core.RawRecordCoverage (rawQueryCtx base queries) calls := by
  have each : ∀ addr heap, (⟨"Ingress::get_ci", [addr], heap⟩ : Call F) ∈ calls →
      ∃ q : RawRecordQuery base.E, q.top = ⟨"Ingress::get_ci", [addr], heap⟩ := by
    intro addr heap member
    obtain ⟨value, after, children, obs, _⟩ := observed.call_observed member
    obtain ⟨a, source, ha, parents⟩ := known addr heap member
    exact ⟨{ addr, result := value, before := heap, after, calls := children, address := a,
      observed := obs, addressRep := ha, source, parents }, rfl⟩
  obtain ⟨queries, covered⟩ := queryList_of_cover base calls each
  exact ⟨queries, rawRecordFacts_of_queries base queries, covered⟩

end IxVM.Refinement.L1
