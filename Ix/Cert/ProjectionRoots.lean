import Ix.Cert.TheoremSnapshots
import Ix.Cert.ReaderClosureKeys
import Ix.Cert.CtxAgree
import Ix.CompileCert.InductiveReading
import Ix.Cert.ProjectionReader

/-! Unwired input projection/owner provenance. A valid projection emits no
declaration; the actual owner read supplies its generated prefix and family.
Emitted-member/key/order guards and family semantics are not supplied here. -/
namespace Ix.Cert.ProjectionRoots
open Ix.Kernel Ix.Kernel.Reader Ix.Kernel.Admission Ix.Cert.AdmittedTargetFronts
def projectionRef : Ixon.ConstantInfo → Option (ConstRef Address)
  | .iPrj p => some (.member p.block p.idx.toNat)
  | .cPrj p => some (.ctor p.block p.idx.toNat p.cidx.toNat)
  | _ => none
def inputOwner (a : Address) : Ingress.Constants → Option (Nat × Ixon.Constant)
  | [] => none
  | (b, c) :: rest => if b == a then some (0, c)
    else (inputOwner a rest).map fun (i, c) => (i + 1, c)
theorem inputOwner_spec {a constants i c} (found : inputOwner a constants = some (i, c)) :
    constants[i]? = some (a, c) ∧ constants.lookup a = some c := by
  induction constants generalizing i with
  | nil => simp [inputOwner] at found
  | cons entry rest ih =>
    obtain ⟨b, d⟩ := entry
    by_cases same : b == a
    · have eq := beq_iff_eq.mp same
      simp only [inputOwner, same, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl⟩ := found
      simp [eq]
    · simp only [inputOwner, same, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at found
      obtain ⟨⟨j, d⟩, earlier, pair⟩ := found
      cases pair
      obtain ⟨indexed, lookup⟩ := ih earlier
      have reverse : (a == b) = false := beq_eq_false_iff_ne.mpr fun h => same (beq_iff_eq.mpr h.symm)
      exact ⟨indexed, by simpa only [List.lookup_cons, reverse] using lookup⟩

structure Located (constants : Ingress.Constants) (j : Nat) where
  address : Address
  root : Ixon.Constant
  reference : ConstRef Address
  ownerPosition : Nat
  owner : Ixon.Constant
  members : Array Ixon.MutConst
  rootAt : constants[j]? = some (address, root)
  projected : projectionRef root.info = some reference
  ownerFound : inputOwner reference.block constants = some (ownerPosition, owner)
  ownerInfo : owner.info = .muts members
  hasInductive : members.any (fun | .indc _ => true | _ => false) = true
  unmixed : members.any (fun | .defn _ => true | _ => false) = false
/-- Missing input owner includes prelude-only owners. No fallback is searched. -/
def locate (constants : Ingress.Constants) (j : Nat) : Except String (Located constants j) := do
  match hroot : constants[j]? with
  | none => throw "projection: input root is unavailable"
  | some (a, c) =>
    match href : projectionRef c.info with
    | none => throw "projection: root is not an inductive or constructor projection"
    | some ref =>
      match howner : inputOwner ref.block constants with
      | none => throw "projection: input owner is unavailable"
      | some (ownerPosition, owner) =>
        match hinfo : owner.info with
        | .muts members =>
          if hi : members.any (fun | .indc _ => true | _ => false) then
            if hn : members.any (fun | .defn _ => true | _ => false) = false then
              return ⟨a, c, ref, ownerPosition, owner, members, hroot, href, howner, hinfo, hi, hn⟩
            else throw "projection: owner mixes inductives and definitions"
          else throw "projection: owner has no inductive family"
        | _ => throw "projection: input owner is not a mutual record"

structure Packet (limits : Limits) (records : Records) (j : Nat) where
  constants : Ingress.Constants
  decoded : decodeRecords limits records = .ok constants
  location : Located constants j

/-- Decode and locate only. Authentication and the actual reader run come
from the genuine receipt in captured, not from an arbitrary Packet. -/
def locateBytes (limits : Limits) (records : Records) (j : Nat) : Except String (Packet limits records j) := do
  match decoded : decodeRecords limits records with
  | .error e => throw s!"projection: {repr e}"
  | .ok constants => return ⟨constants, decoded, ← locate constants j⟩

private theorem lowered {md : Mode} {cx : Ctx md} {st : State md} {a : Address}
    {c : Ixon.Constant} {ms : Array Ixon.MutConst} {r : Read md}
    (run : readInductive cx st a c ms = .ok r) :
    ∃ shape rb, cx.index.blocks[a]? = some shape ∧ lowerInductive st rb = .ok r := by
  rw [Ix.CompileCert.InductiveReading.readInductive_eq] at run
  unfold Ix.CompileCert.InductiveReading.readInductiveSpec at run
  cases found : cx.index.blocks[a]? with
  | none =>
    simp only [found, declined, throw, throwThe, MonadExceptOf.throw] at run
    cases run
  | some shape =>
    simp only [found] at run
    iterate 4 all_goals first
      | contradiction
      | (split at run <;> try simp only [malformed, declined, throw, throwThe, MonadExceptOf.throw, Except.bind, bind] at run)
    all_goals first
      | contradiction
      | (obtain ⟨types, _, run⟩ := Ix.CompileCert.Loop.except_bind_ok.mp run
         obtain ⟨ctors, _, run⟩ := Ix.CompileCert.Loop.except_bind_ok.mp run
         obtain ⟨recs, _, run⟩ := Ix.CompileCert.Loop.except_bind_ok.mp run
         exact ⟨shape, _, rfl, run⟩)

private theorem projection_empty {md : Mode} {cx : Ctx md} {st : State md} {a : Address}
    {c : Ixon.Constant} {ref : ConstRef Address} {r : Read md}
    (projected : projectionRef c.info = some ref) (run : readRecord cx st a c = .ok r) : r.decls = #[] := by
  cases info : c.info <;> simp only [projectionRef, info, reduceCtorEq] at projected
  all_goals
    simp only [readRecord, info] at run
    split at run
    · simp only [malformed, throw, throwThe, MonadExceptOf.throw] at run; cases run
    · simp only [pure, Except.pure, Except.ok.injEq] at run
      subst r; rfl

/-- Same receipt, canonical decoded input and actual reader walk. The owner
emits generated declarations followed by its own literal family declaration;
this does not yet assert that the selected projection is an emitted member. -/
theorem captured {binding limits records blobs hint receipt j}
    (accepted : DefinitionSnapshots.checkReceipt binding limits records blobs hint = .ok receipt)
    (packet : Packet limits records j)
    (_produced : locateBytes limits records j = .ok packet) :
    ∃ p : Prepared binding limits records blobs hint receipt.env,
      p.constants = packet.constants ∧ p.table = receipt.table ∧ p.pre = receipt.pre ∧
      p.ev = receipt.ev ∧ Frontend.preparePrelude p.pre.ix p.decls = receipt.ds ∧
      let l := packet.location
      let cx := streamContext Address.admissionHash p.table p.pre p.constants blobs hint
      ∃ fin rootState rootRead ownerState ownerRead,
      ∃ shape : BlockShape, ∃ rb : BlockRead .anon, ∃ gens : List (Declaration .anon),
        StreamRead cx p.pre.state p.constants fin p.decls ∧
        RecordAt cx p.pre.state fin p.constants p.decls j l.address l.root rootState rootRead ∧
        rootRead.decls = #[] ∧
        RecordAt cx p.pre.state fin p.constants p.decls l.ownerPosition l.reference.block l.owner ownerState ownerRead ∧
        cx.store l.reference.block = some l.owner ∧
        readInductive cx ownerState l.reference.block l.owner l.members = .ok ownerRead ∧
        cx.index.blocks[l.reference.block]? = some shape ∧ lowerInductive ownerState rb = .ok ownerRead ∧
        ownerRead.decls = gens.toArray.push (CtxAgree.indDeclOf rb) ∧ ownerRead.generated = gens.length := by
  obtain ⟨p, table, pre, ev, ds⟩ := TheoremSnapshots.prepared_of_receipt accepted
  have constants := Except.ok.inj (p.decoded.symm.trans packet.decoded)
  obtain ⟨fin, stream, _, _⟩ := readStream_spec p.read
  let l := packet.location
  have rootAt : p.constants[j]? = some (l.address, l.root) := constants.symm ▸ l.rootAt
  obtain ⟨ownerAt, lookup⟩ := inputOwner_spec l.ownerFound
  have ownerAt' : p.constants[l.ownerPosition]? = some (l.reference.block, l.owner) := constants.symm ▸ ownerAt
  obtain ⟨rootState, rootRead, rootTrace⟩ := stream_at stream rootAt
  obtain ⟨ownerState, ownerRead, ownerTrace⟩ := stream_at stream ownerAt'
  have rootEmpty := projection_empty l.projected rootTrace.2.choose_spec.choose_spec.2.1
  have stored : (streamContext Address.admissionHash p.table p.pre p.constants blobs hint).store l.reference.block = some l.owner := by
    have hit : (recordMap p.constants.toArray)[l.reference.block]? = some l.owner := by
      rw [ReaderClosureKeys.recordMap_get, List.toList_toArray, constants]
      exact lookup
    change ((recordMap p.constants.toArray)[l.reference.block]? <|> _) = some l.owner
    rw [hit]; rfl
  have read := ownerTrace.2.choose_spec.choose_spec.2.1
  have family := (owner_read_eq l.ownerInfo l.hasInductive l.unmixed).symm.trans read
  obtain ⟨shape, rb, found, loweredRun⟩ := lowered family
  obtain ⟨gens, emitted, count, _, _⟩ := CtxAgree.lowerInductive_ok loweredRun
  exact ⟨p, constants, table, pre, ev, ds, fin, rootState, rootRead, ownerState, ownerRead,
    shape, rb, gens, stream, rootTrace, rootEmpty, ownerTrace, stored, family, found, loweredRun, emitted, count⟩

end Ix.Cert.ProjectionRoots
