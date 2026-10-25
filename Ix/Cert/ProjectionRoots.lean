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

open Ix.CompileCert.InductiveReading
private def observed {ε α : Type} (x : Except ε α) : Except ε { a // x = .ok a } :=
  match x with | .error e => .error e | .ok a => .ok ⟨a, rfl⟩
private theorem observed_bind {ε α β : Type} (x : Except ε α) (f : α → Except ε β) :
    (observed x >>= fun a => f a.val) = (x >>= f) := by cases x <;> rfl
private theorem observed_loops {md : Mode} (st : State md) (n : Nat)
    (x : ReadM (Array (CVal md × Nat × Nat))) (y : ReadM (Array (CVal md × Nat × Nat) × Array (List (CName md))))
    (z : ReadM (Array (CVal md × RecCounts × List (Ix.Kernel.RecRule md)))) :
    (do let a ← observed x; let b ← observed y; let c ← observed z; lowerInductive st ⟨n, a.val, b.val.1, b.val.2, c.val⟩) =
      (do let a ← x; let b ← y; let c ← z; lowerInductive st ⟨n, a, b.1, b.2, c⟩) := by cases x <;> cases y <;> cases z <;> rfl

structure Trace {md : Mode} (cx : Ctx md) (st : State md) (a : Address) (c : Ixon.Constant) (ms : Array Ixon.MutConst) where
  shape : BlockShape
  first : Nat × Ixon.Inductive
  rb : BlockRead md
  read : Read md
  found : cx.index.blocks[a]? = some shape
  head : (shape.order.filterMap (indcAt ms))[0]? = some first
  params : rb.numParams = first.2.params.toNat
  types : forIn (shape.order.filterMap (indcAt ms)) #[] (typeStep cx a (.mk' cx c id (blockSelf cx a ms))) = .ok rb.types
  ctors : forIn (shape.order.filterMap (indcAt ms)) (#[], #[]) (ctorClassStep cx a (.mk' cx c id (blockSelf cx a ms)) rb.numParams) = .ok (rb.ctors, rb.ctorNames)
  recs : readRecursors cx (List.range first.2.lvls.toNat) shape.recs = .ok rb.recs
  lowered : lowerInductive st rb = .ok read
/-- Retain the actual loop outputs; their equations erase at runtime. -/
def traceOwner {md : Mode} (cx : Ctx md) (st : State md) (a : Address) (c : Ixon.Constant)
    (ms : Array Ixon.MutConst) : ReadM (Trace cx st a c ms) := do
  match hs : cx.index.blocks[a]? with
  | none => declined "inductive block without a recursor in the input"
  | some shape =>
    let indcs := shape.order.filterMap (indcAt ms)
    unless indcs.size == shape.order.size do malformed "recursor motive is not a member of its block"
    match hf : indcs[0]? with
    | none => malformed "empty inductive block"
    | some first =>
      if indcs.any (·.2.isUnsafe) then declined "unsafe inductive declaration"
      let nPd := first.2.params.toNat
      unless indcs.all (·.2.params.toNat == nPd) do declined "inductive block whose type records disagree on numParams"
      let mr := MemberReader.mk' cx c id (blockSelf cx a ms)
      let types ← observed (forIn indcs #[] (typeStep cx a mr))
      let ctors ← observed (forIn indcs (#[], #[]) (ctorClassStep cx a mr nPd))
      let recs ← observed (readRecursors cx (List.range first.2.lvls.toNat) shape.recs)
      let rb : BlockRead md := ⟨nPd, types.val, ctors.val.1, ctors.val.2, recs.val⟩
      let out ← observed (lowerInductive st rb)
      return { shape, first, rb, read := out.val, found := hs, head := hf, params := rfl,
               types := by simpa only [rb] using types.property,
               ctors := by simpa only [rb] using ctors.property,
               recs := by simpa only [rb] using recs.property, lowered := out.property }
theorem traceOwner_read {md : Mode} (cx : Ctx md) (st : State md) (a : Address)
    (c : Ixon.Constant) (ms : Array Ixon.MutConst) :
    (traceOwner cx st a c ms).map (·.read) = readInductive cx st a c ms := by
  change (fun t => t.read) <$> traceOwner cx st a c ms = _
  rw [readInductive_eq]
  unfold traceOwner readInductiveSpec
  iterate 5 all_goals first
    | rfl
    | (split <;> try simp_all only [map_bind, map_pure, observed_bind, bind_pure])
  all_goals first
    | rfl
    | (rename_i shape hs size first hf safe params
       exact observed_loops st first.2.params.toNat _ _ _)
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
  obtain ⟨tr, _, rfl⟩ := Except.map_eq_ok ((traceOwner_read _ _ _ _ _).trans family)
  obtain ⟨gens, emitted, count, _, _⟩ := CtxAgree.lowerInductive_ok tr.lowered
  exact ⟨p, constants, table, pre, ev, ds, fin, rootState, rootRead, ownerState, tr.read,
    tr.shape, tr.rb, gens, stream, rootTrace, rootEmpty, ownerTrace, stored, family, tr.found, tr.lowered, emitted, count⟩
def prefixState {md : Mode} (cx : Ctx md) : State md → Ingress.Constants → ReadM (State md)
  | st, [] => pure st
  | st, (a, c) :: rest => do let r ← readRecord cx st a c; prefixState cx (st.commit r) rest
private theorem prefixState_eq {md : Mode} {cx : Ctx md} {st fin constants decls}
    (run : StreamRead cx st constants fin decls) : prefixState cx st constants = .ok fin := by
  induction run with
  | nil => rfl
  | cons read tail ih => simp only [prefixState, read, bind, Except.bind, ih]
def scanOwner {md : Mode} {constants j} (cx : Ctx md) (start : State md) (l : Located constants j) :
    ReadM (Σ st, Trace cx st l.reference.block l.owner l.members) := do
  let st ← prefixState cx start (constants.take l.ownerPosition)
  return ⟨st, ← traceOwner cx st l.reference.block l.owner l.members⟩
theorem scanOwner_same {binding limits records blobs hint receipt j}
    (accepted : DefinitionSnapshots.checkReceipt binding limits records blobs hint = .ok receipt)
    (packet : Packet limits records j) (produced : locateBytes limits records j = .ok packet) :
    let l := packet.location; let cx := streamContext Address.admissionHash receipt.table receipt.pre packet.constants blobs hint
    ∃ fin decls st, ∃ tr : Trace cx st l.reference.block l.owner l.members,
      RecordAt cx receipt.pre.state fin packet.constants decls l.ownerPosition l.reference.block l.owner st tr.read ∧
      Frontend.preparePrelude receipt.pre.ix decls = receipt.ds ∧ scanOwner cx receipt.pre.state l = .ok ⟨st, tr⟩ := by
  obtain ⟨p, cs, table, pre, _, ds, fin, _, _, st, r, _, _, _, _, _, _, atOwner, _, family, _, _, _, _⟩ := captured accepted packet produced
  simp only [cs, table, pre] at atOwner family ds
  obtain ⟨tr, run, same⟩ := Except.map_eq_ok ((traceOwner_read _ _ _ _ _).trans family)
  refine ⟨fin, p.decls, st, tr, ?_, ds, ?_⟩
  · simpa only [same] using atOwner
  · rw [scanOwner, prefixState_eq atOwner.2.choose_spec.choose_spec.1]; simp only [bind, Except.bind, run, pure, Except.pure]

end Ix.Cert.ProjectionRoots
