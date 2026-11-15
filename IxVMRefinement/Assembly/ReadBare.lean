import IxVMRefinement.Assembly.Closure
import Ix.Cert.Stream
import Ix.Cert.ReaderUnits
import Ix.Cert.CtxAgreeProjFields
import Ix.Cert.SourceNames
import Ix.Cert.EvidenceTransfer
import Ix.Cert.ReadingKeys
import IxC.Ixon.Verify.BoundedConstant
import IxC.Kernel.Model.Restrict

/-! # Bare stream reader completeness, empty `projLevels`, and structural `DeclNonAux`

Proves completeness and structural properties of `Ix.Kernel.Admission.prepareBare` and
`Ix.Kernel.Reader.readRecordsBare` over the sub-store closure `(E, order)`:

* `decodeLoopBare_complete`, `decodeRecordsBare_complete`, `closure_readsBare`, and
  `closure_decodesBare`: bounded exact decoding (`Ixon.Bounded.deConstant`) succeeds on
  `Ix.Cert.recordsOf E order` under chosen batch/record limits whenever every stored record in `E`
  decodes via `Ixon.deConstantExact` — with zero canonical-re-encoding requirement;
* `StreamReadBare`, `readRecordsBare_complete`, `readStreamBare_complete`, `prepareBare_ok`, and
  `readIn_of_streamReadBare`: record-by-record bare reading discharges `IxVM.Consistency.ReadIn`;
* `preludeFor_projLevels_empty`, `streamReadBare_projLevels_empty`, and `projRewrite_eq_none`:
  neither `preludeFor` nor `readRecordsBare` ever generates `_model` declarations (`generated = 0`),
  so `st.projLevels` remains empty throughout reading and `projRewrite` is identically `none`;
* `NonAuxKey`, `ConstantInfoNonAux`, `DeclNonAux`, and `preparePrelude_declNonAux`: every
  declaration in `preparePrelude pre.ix decls` installs pairwise-distinct non-auxiliary keys whose
  types, values, and recursor rules reference only non-auxiliary keys;
* `resolve_inj_singleton`, `streamContext_memberKey_addressKey`, and
  `inertKey_false_of_addressKey_not_inert`: key-origin helpers connecting `Ctx.memberKey` to
  `IxVM.Refinement.AddressKey` and `IxVM.Consistency.InertAt`. -/

namespace IxVM.Refinement.Assembly

open Ix.Kernel (ConstRef Mode)
open Ix.Kernel.Admission (Limits Records Binding)
open Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok)
open Ix.Cert.ReaderUnits (ite_ok fail_bind throw_ok forIn_pushes RolesKeyed)

/-! ## Bounded exact record decoding (`decodeRecordsBare`) and byte-stage completeness -/

/-- One record `(addr, bytes)` decodes under `limits` to `(addr, c)` via `Ixon.Bounded.deConstant`. -/
def RecordReadBare (limits : Limits)
    (record : _root_.Address × ByteArray) (constant : _root_.Address × Ixon.Constant) : Prop :=
  record.1 = constant.1 ∧
  record.2.size ≤ limits.maxRecordBytes ∧
  Ixon.Bounded.univNodes constant.2.univs ≤ limits.maxRecordUnivNodes ∧
  Ixon.deConstantExact record.2 = .ok constant.2

/-- Stream-level relation for `decodeRecordsBare`. -/
abbrev RecordsReadBare (limits : Limits)
    (records : Records) (constants : Ix.Kernel.Ingress.Constants) : Prop :=
  List.Forall₂ (RecordReadBare limits) records constants

theorem RecordsReadBare.keys {limits : Limits}
    {records : Records} {constants : Ix.Kernel.Ingress.Constants}
    (h : RecordsReadBare limits records constants) :
    constants.map Prod.fst = records.map Prod.fst := by
  induction h with
  | nil => rfl
  | cons hd _ ih => simp only [List.map_cons, hd.1, ih]

theorem decodeLoopBare_complete (limits : Limits) :
    ∀ {records : Records} {constants : Ix.Kernel.Ingress.Constants},
      RecordsReadBare limits records constants →
      ∀ (pos : Nat) (rev : Ix.Kernel.Ingress.Constants),
        Ix.Kernel.Admission.decodeLoopBare limits pos records rev =
          .ok (rev.reverse ++ constants)
  | _, _, .nil, _, rev => by
    simp [Ix.Kernel.Admission.decodeLoopBare]
  | (addr, bytes) :: _, (addr', c) :: cs, .cons ⟨hkey, hbytes, hnodes, hexact⟩ htail, pos, rev => by
    subst hkey
    have hdec :
        Ixon.Bounded.deConstant limits.maxRecordBytes limits.maxRecordUnivNodes bytes = .ok c :=
      Ixon.Verify.BoundedConstant.deConstant_complete _ _ bytes c hexact hbytes hnodes
    simp only [Ix.Kernel.Admission.decodeLoopBare, hdec, Except.mapError, bind, Except.bind]
    rw [decodeLoopBare_complete limits htail (pos + 1) ((addr, c) :: rev)]
    simp [List.reverse_cons, List.append_assoc]

theorem decodeRecordsBare_complete {limits : Limits}
    {records : Records} {constants : Ix.Kernel.Ingress.Constants}
    (h : RecordsReadBare limits records constants) :
    Ix.Kernel.Admission.decodeRecordsBare limits records = .ok constants := by
  unfold Ix.Kernel.Admission.decodeRecordsBare
  simpa using decodeLoopBare_complete limits h 0 []

/-- Every stored record of `order` in `E` decodes via `RecordsReadBare` whenever `limits` bounds
each record's byte size and universe-node count and `E.consts` decodes via `deConstantExact`. -/
theorem closure_readsBare (E : Ixon.Env) (limits : Limits) :
    ∀ (order : List _root_.Address),
      (∀ a ∈ order, ∀ lc, E.consts.get? a = some lc →
        ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c) →
      (∀ entry ∈ Ix.Cert.recordsOf E order, entry.2.size ≤ limits.maxRecordBytes) →
      (∀ entry ∈ Ix.Cert.Stream.decodedOf E order,
        Ixon.Bounded.univNodes entry.2.univs ≤ limits.maxRecordUnivNodes) →
      RecordsReadBare limits (Ix.Cert.recordsOf E order) (Ix.Cert.Stream.decodedOf E order)
  | [], _, _, _ => by
    simp [Ix.Cert.recordsOf, Ix.Cert.Stream.decodedOf]
  | a :: order, hdec, bytesFit, nodesFit => by
    have tail := closure_readsBare E limits order
      (fun b hb => hdec b (List.mem_cons_of_mem _ hb))
      (fun e he => bytesFit e (by
        rw [Ix.Cert.Stream.recordsOf_cons]; exact List.mem_append_right _ he))
      (fun e he => nodesFit e (by
        rw [Ix.Cert.Stream.decodedOf_cons]; exact List.mem_append_right _ he))
    rw [Ix.Cert.Stream.recordsOf_cons, Ix.Cert.Stream.decodedOf_cons]
    cases hl : E.consts.get? a with
    | none =>
      have hr : Ix.Cert.recordAt E a = none := by unfold Ix.Cert.recordAt; rw [hl]; rfl
      simpa [hr] using tail
    | some lc =>
      obtain ⟨c, hc, hexact⟩ := hdec a List.mem_cons_self lc hl
      have hr : Ix.Cert.recordAt E a = some c := by unfold Ix.Cert.recordAt; rw [hl]; exact hc
      simp only [Option.map_some, Option.toList_some, hr, List.singleton_append]
      refine .cons ⟨rfl, ?_, ?_, hexact⟩ tail
      · exact bytesFit (a, lc.rawBytes) (by rw [Ix.Cert.Stream.recordsOf_cons, hl]; simp)
      · exact nodesFit (a, c) (by rw [Ix.Cert.Stream.decodedOf_cons, hr]; simp)

/-- Existential `Limits` witness for `WithinBatch` and `RecordsReadBare` on `(E, order)`. -/
theorem closure_decodesBare (E : Ixon.Env) {order : List _root_.Address}
    (hdec : ∀ a ∈ order, ∀ lc, E.consts.get? a = some lc →
      ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c) :
    ∃ limits : Limits,
      Ix.Kernel.Admission.WithinBatch limits (Ix.Cert.recordsOf E order) (Ix.Cert.blobsOf E order) ∧
      RecordsReadBare limits (Ix.Cert.recordsOf E order) (Ix.Cert.Stream.decodedOf E order) := by
  let records := Ix.Cert.recordsOf E order
  let blobs := Ix.Cert.blobsOf E order
  let limits : Limits :=
    { maxRecords := records.length
      maxBlobs := blobs.length
      maxTotalBytes := Ix.Kernel.Admission.payloadBytes records + Ix.Kernel.Admission.payloadBytes blobs
      maxRecordBytes := Ix.Kernel.Admission.payloadBytes records
      maxRecordUnivNodes := Ix.Cert.Stream.nodesOf (Ix.Cert.Stream.decodedOf E order) }
  refine ⟨limits, ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩, ?_⟩
  exact closure_readsBare E limits order hdec
    (fun _ h => Ix.Cert.Stream.size_le_payload h)
    (fun _ h => Ix.Cert.Stream.nodes_le h)

/-- Pure-BLAKE3 authentication of `recordsOf E order` and `blobsOf E order` from `E`'s invariants. -/
theorem closure_authentic_of_env (E : Ixon.Env) (order : List _root_.Address)
    (hrec : ∀ a lc, E.consts.get? a = some lc → _root_.Address.blake3Pure lc.rawBytes = a)
    (hblob : ∀ a bytes, E.blobs.get? a = some bytes → _root_.Address.blake3Pure bytes = a) :
    Ix.Kernel.Admission.Authentic _root_.Address.admissionHash
      (Ix.Cert.recordsOf E order) (Ix.Cert.blobsOf E order) := by
  rw [_root_.Address.admissionHash_eq]
  refine ⟨fun entry hm => ?_, fun entry hm => ?_⟩
  · obtain ⟨-, lc, hl, he⟩ := Ix.Cert.Stream.mem_recordsOf hm
    rw [he]
    exact (hrec entry.1 lc hl).symm
  · exact (hblob entry.1 entry.2 (Ix.Cert.Stream.mem_blobsOf hm)).symm

/-! ## `StreamReadBare`, `readRecordsBare_complete`, `prepareBare_ok`, and `readIn_of_streamReadBare` -/

/-- Record-by-record bare stream reading (`readRecordBare` threaded via `State.commit`). -/
inductive StreamReadBare {md : Mode} (cx : Ctx md) :
    State md → List (_root_.Address × Ixon.Constant) → State md → Array (CDecl md) → Prop where
  | nil {st : State md} : StreamReadBare cx st [] st #[]
  | cons {st st' : State md} {a : _root_.Address} {c : Ixon.Constant} {r : Read md}
      {rest : List (_root_.Address × Ixon.Constant)} {out : Array (CDecl md)}
      (read : readRecordBare cx st a c = .ok r)
      (tail : StreamReadBare cx (st.commit r) rest st' out) :
      StreamReadBare cx st ((a, c) :: rest) st' (r.decls ++ out)

theorem StreamReadBare.mem {md : Mode} {cx : Ctx md} {st st' : State md}
    {records : List (_root_.Address × Ixon.Constant)} {out : Array (CDecl md)}
    (h : StreamReadBare cx st records st' out)
    {a : _root_.Address} {c : Ixon.Constant} (hm : (a, c) ∈ records) :
    ∃ st₀ r, readRecordBare cx st₀ a c = .ok r ∧ ∀ d ∈ r.decls, d ∈ out := by
  induction h with
  | nil => nomatch hm
  | @cons st _ _ _ r _ _ read _ ih =>
    rcases List.mem_cons.mp hm with same | hm
    · cases same
      exact ⟨st, r, read, fun d hd => Array.mem_append_left _ hd⟩
    · obtain ⟨st₀, r₀, h₀, hd⟩ := ih hm
      exact ⟨st₀, r₀, h₀, fun d hd' => Array.mem_append_right _ (hd d hd')⟩

theorem streamReadBare_cons_inv {md : Mode} {cx : Ctx md} {st st' : State md}
    {a : _root_.Address} {c : Ixon.Constant}
    {rest : List (_root_.Address × Ixon.Constant)} {out : Array (CDecl md)}
    (h : StreamReadBare cx st ((a, c) :: rest) st' out) :
    ∃ r out', readRecordBare cx st a c = .ok r ∧
      StreamReadBare cx (st.commit r) rest st' out' ∧
      out = r.decls ++ out' := by
  cases h with
  | cons read tail => exact ⟨_, _, read, tail, rfl⟩

theorem streamReadBare_lowerings {md : Mode} {cx : Ctx md} {st st' : State md}
    {records : List (_root_.Address × Ixon.Constant)} {out : Array (CDecl md)}
    (h : StreamReadBare cx st records st' out) :
    ∃ rs : List (Read md),
      List.Forall₂
        (fun (x : _root_.Address × Ixon.Constant) r => ∃ st₀, readRecordBare cx st₀ x.1 x.2 = .ok r)
        records rs ∧
      out.toList = (rs.map fun r => r.decls.toList).flatten := by
  induction h with
  | nil => exact ⟨[], .nil, rfl⟩
  | @cons st _ _ _ r _ _ read _ ih =>
    obtain ⟨rs, holds, flat⟩ := ih
    exact ⟨r :: rs, .cons ⟨st, read⟩ holds, by simp [flat]⟩

theorem forIn_completeBare {md : Mode} {cx : Ctx md}
    {f : (_root_.Address × Ixon.Constant) × Nat →
      Std.HashSet _root_.Address × State md × Array (CDecl md) →
      Except (ReadError × Nat)
        (ForInStep (Std.HashSet _root_.Address × State md × Array (CDecl md)))}
    (hf : ∀ x s r, s.1.contains x.1.1 = false → readRecordBare cx s.2.1 x.1.1 x.1.2 = .ok r →
      f x s = .ok (.yield (s.1.insert x.1.1, s.2.1.commit r, s.2.2 ++ r.decls))) :
    ∀ (l : List ((_root_.Address × Ixon.Constant) × Nat))
      (s : Std.HashSet _root_.Address × State md × Array (CDecl md))
      (st' : State md) (out : Array (CDecl md)),
      StreamReadBare cx s.2.1 (l.map Prod.fst) st' out →
      (l.map (·.1.1)).Nodup →
      (∀ y ∈ l, s.1.contains y.1.1 = false) →
      ∃ seen, forIn l s f = .ok (seen, st', s.2.2 ++ out) := by
  intro l
  induction l with
  | nil =>
    intro s st' out reads _ _
    cases reads
    exact ⟨s.1, by simp [pure, Except.pure]⟩
  | cons x l ih =>
    intro s st' out reads keys fresh
    obtain ⟨⟨a, c⟩, i⟩ := x
    obtain ⟨r, out', read, tail, rfl⟩ := streamReadBare_cons_inv reads
    have hx : s.1.contains a = false := fresh _ List.mem_cons_self
    rw [List.forIn_cons, hf ((a, c), i) s r hx read]
    simp only [bind, Except.bind]
    have keys' := List.nodup_cons.mp keys
    obtain ⟨seen, ran⟩ := ih (s.1.insert a, s.2.1.commit r, s.2.2 ++ r.decls) st' out' tail keys'.2
      (fun y hy => by
        rw [Std.HashSet.contains_insert, Bool.or_eq_false_iff]
        refine ⟨?_, fresh y (List.mem_cons_of_mem _ hy)⟩
        rw [beq_eq_false_iff_ne]
        intro same
        exact keys'.1 (List.mem_map.2 ⟨y, hy, same.symm⟩))
    exact ⟨seen, by rw [ran]; simp [Array.append_assoc]⟩

theorem readRecordsBare_loop {md : Mode} {cx : Ctx md}
    {f : (_root_.Address × Ixon.Constant) × Nat →
      Std.HashSet _root_.Address × State md × Array (CDecl md) →
      Except (ReadError × Nat)
        (ForInStep (Std.HashSet _root_.Address × State md × Array (CDecl md)))}
    (hf : ∀ x s r, s.1.contains x.1.1 = false → readRecordBare cx s.2.1 x.1.1 x.1.2 = .ok r →
      f x s = .ok (.yield (s.1.insert x.1.1, s.2.1.commit r, s.2.2 ++ r.decls)))
    {st st' : State md} {records : List (_root_.Address × Ixon.Constant)} {out : Array (CDecl md)}
    (reads : StreamReadBare cx st records st' out)
    (keys : (records.map Prod.fst).Nodup) :
    (forIn records.zipIdx (({} : Std.HashSet _root_.Address), st, (#[] : Array (CDecl md))) f >>=
      fun s => pure (s.2.1, s.2.2)) = (.ok (st', out) : Except (ReadError × Nat) _) := by
  have zipped : (records.zipIdx.map Prod.fst) = records := by simp
  obtain ⟨seen, ran⟩ := forIn_completeBare hf records.zipIdx ({}, st, #[]) st' out
    (by rw [zipped]; exact reads)
    (by
      have : records.zipIdx.map (·.1.1) = records.map Prod.fst := by
        rw [show (fun y : (_root_.Address × Ixon.Constant) × Nat => y.1.1) =
          Prod.fst ∘ Prod.fst from rfl, ← List.map_map, zipped]
      rw [this]
      exact keys)
    (fun _ _ => by simp)
  rw [ran]
  simp [bind, Except.bind, pure, Except.pure]

theorem readRecordsBare_complete {md : Mode} {cx : Ctx md} {st st' : State md}
    {records : List (_root_.Address × Ixon.Constant)} {out : Array (CDecl md)}
    (reads : StreamReadBare cx st records st' out)
    (keys : (records.map Prod.fst).Nodup) :
    readRecordsBare cx st records.toArray = .ok (st', out) := by
  unfold readRecordsBare
  dsimp only
  rw [← Array.forIn_toList, Array.toList_zipIdx, List.toList_toArray]
  refine readRecordsBare_loop ?_ reads keys
  intro x s r hx hr
  simp [hx, hr, pure, Except.pure]

theorem readStreamBare_complete {hash : ByteArray → _root_.Address}
    {t : Ix.Kernel.RoleTable} {pre : Prelude .anon}
    {constants : List (_root_.Address × Ixon.Constant)} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef _root_.Address → Option Ix.Kernel.ReducibilityHint}
    {st' : State .anon} {decls : Array (CDecl .anon)}
    (reads : StreamReadBare (Ix.Kernel.Admission.streamContext hash t pre constants blobs hint)
      pre.state constants st' decls)
    (keys : (constants.map Prod.fst).Nodup)
    (keeps : State.keepsPrelude pre.state st' = true) :
    Ix.Kernel.Admission.readStreamBare hash t pre constants blobs hint =
      .ok (evidenceOf (Ix.Kernel.Admission.streamContext hash t pre constants blobs hint) st' t,
        decls) := by
  unfold Ix.Kernel.Admission.readStreamBare
  dsimp only
  rw [readRecordsBare_complete reads keys]
  simp [keeps, pure, Except.pure]

theorem prepareBare_ok {hash : ByteArray → _root_.Address} {binding : Binding}
    {pre : Prelude .anon} {limits : Limits} {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef _root_.Address → Option Ix.Kernel.ReducibilityHint}
    {t : Ix.Kernel.RoleTable} {constants : List (_root_.Address × Ixon.Constant)}
    {st' : State .anon} {decls : Array (CDecl .anon)}
    (batch : Ix.Kernel.Admission.WithinBatch limits records blobs)
    (unique : Ix.Kernel.Admission.UniqueKeys records blobs)
    (authentic : Ix.Kernel.Admission.Authentic hash records blobs)
    (admitted : Ix.Kernel.Admission.admitBinding hash binding = .ok t)
    (decoded : RecordsReadBare limits records constants)
    (reads : StreamReadBare (Ix.Kernel.Admission.streamContext hash t pre constants blobs hint)
      pre.state constants st' decls)
    (keeps : State.keepsPrelude pre.state st' = true) :
    Ix.Kernel.Admission.prepareBare hash binding pre limits records blobs hint =
      .ok (evidenceOf (Ix.Kernel.Admission.streamContext hash t pre constants blobs hint) st' t,
        Ix.Kernel.Frontend.preparePrelude pre.ix decls) := by
  have hp := (Ix.Kernel.Admission.preflight_ok_iff limits records blobs).mpr batch
  have hu := (Ix.Kernel.Admission.uniqueKeys_ok_iff records blobs).mpr unique
  have ha := (Ix.Kernel.Admission.authenticate_ok_iff hash records blobs).mpr authentic
  have hd := decodeRecordsBare_complete decoded
  have keys : (constants.map Prod.fst).Nodup := by
    rw [decoded.keys]
    exact unique.1
  have hs := readStreamBare_complete reads keys keeps
  unfold Ix.Kernel.Admission.prepareBare
  simp only [hp, hu, ha, admitted, hd, hs, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- **`ReadIn` from `StreamReadBare`**: given an admitted binding `b → t`, a `UsedClosureOrderAt`
order `order`, `preludeFor t = .ok pre`, pure-BLAKE3 authenticated and exact-decoded `E`, and a
`StreamReadBare` on `decodedOf E order` keeping `pre.state`, `ReadIn` holds unconditionally. -/
theorem readIn_of_streamReadBare {b : Binding} {E : Ixon.Env} {seeds : _root_.Address → Prop}
    {t : Ix.Kernel.RoleTable} {order : List _root_.Address} {pre : Prelude .anon}
    {st' : State .anon} {decls : Array (CDecl .anon)}
    (hadm : Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok t)
    (hord : IxVM.Consistency.UsedClosureOrderAt t E
      (fun a => seeds a ∨ ∃ e ∈ t.evidence.toList, Ix.Kernel.Evidence.proof a ∈ e.2.toList) order)
    (hpre : preludeFor t = .ok pre)
    (hauth_rec : ∀ a lc, E.consts.get? a = some lc → _root_.Address.blake3Pure lc.rawBytes = a)
    (hauth_blob : ∀ a bytes, E.blobs.get? a = some bytes → _root_.Address.blake3Pure bytes = a)
    (hdec : ∀ a ∈ order, ∀ lc, E.consts.get? a = some lc →
      ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c)
    (hreads : StreamReadBare
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
        (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
      pre.state (Ix.Cert.Stream.decodedOf E order) st' decls)
    (hkeeps : State.keepsPrelude pre.state st' = true) :
    IxVM.Consistency.ReadIn b E seeds
      (evidenceOf
        (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
          (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
        st' t)
      (Ix.Kernel.Frontend.preparePrelude pre.ix decls) := by
  obtain ⟨limits, hbatch, hdecoded⟩ := closure_decodesBare E hdec
  refine ⟨t, order, pre, limits, hadm, hord, hpre, ?_⟩
  exact prepareBare_ok hbatch (Ix.Cert.Stream.closure_unique E hord.nodup)
    (closure_authentic_of_env E order hauth_rec hauth_blob) hadm hdecoded hreads hkeeps

/-! ## Empty `projLevels` (`projRewrite = none`) across `preludeFor` and `StreamReadBare` -/

theorem projLevels_commit_of_generated_zero {md : Mode} (st : State md) {r : Read md}
    (hg : r.generated = 0) :
    (st.commit r).projLevels = st.projLevels := by
  rw [Ix.Cert.CtxAgree.commit_projLevels]
  simp [Ix.Cert.CtxAgree.levelEntries, hg]

theorem projRewrite_eq_none {md : Mode} {st : State md}
    (hemp : ∀ k : CName md, st.projLevels[k]? = none)
    (cv : CVal md) (value : CExpr md) :
    projRewrite st cv value = none := by
  unfold projRewrite
  split
  · rename_i T i _
    cases st.projOwners[T]? with
    | none => rfl
    | some o =>
      cases (cv.levelParams == o.lps) <;> simp [hemp, guard, failure]
  · rfl

/-- Exact shape of `lowerInductiveDeclsBare`: `generated = 0` and a single `.indDecl`. -/
theorem lowerInductiveDeclsBare_spec {md : Mode} {rb : BlockRead md} {r : Read md}
    (h : lowerInductiveDeclsBare rb = .ok r) :
    let block : List (CInfo md) :=
      (rb.types.toList.map fun x => .indInfo x.1 {}) ++
      (rb.ctors.toList.map fun x => .ctorInfo x.1 x.2.1 x.2.2) ++
      (rb.recs.toList.map fun x =>
        .recInfo x.1 (x.2.1.params + x.2.1.motives + x.2.1.minors + x.2.1.indices)
          (x.2.1.params + x.2.1.motives + x.2.1.minors) x.2.2)
    r.generated = 0 ∧ r.decls = #[.indDecl block rb.numParams] := by
  obtain ⟨nPd, types, ctors, ctorNames, recs⟩ := rb
  unfold lowerInductiveDeclsBare at h
  simp only [ite_not, bne_iff_ne, ne_eq] at h
  split at h
  all_goals
    rcases ite_ok h with h | h
    all_goals obtain ⟨_, -, h⟩ := except_bind_ok.mp h
    all_goals
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩

/-- Exact shape of `lowerInductiveBare`: `generated = 0`, single `.indDecl`, and distinct names. -/
theorem lowerInductiveBare_spec {md : Mode} {rb : BlockRead md} {r : Read md}
    (h : lowerInductiveBare rb = .ok r) :
    let block : List (CInfo md) :=
      (rb.types.toList.map fun x => .indInfo x.1 {}) ++
      (rb.ctors.toList.map fun x => .ctorInfo x.1 x.2.1 x.2.2) ++
      (rb.recs.toList.map fun x =>
        .recInfo x.1 (x.2.1.params + x.2.1.motives + x.2.1.minors + x.2.1.indices)
          (x.2.1.params + x.2.1.motives + x.2.1.minors) x.2.2)
    r.generated = 0 ∧
    r.decls = #[.indDecl block rb.numParams] ∧
    (block.map (·.name)).Nodup := by
  unfold lowerInductiveBare at h
  obtain ⟨r₀, hr₀, h⟩ := except_bind_ok.mp h
  obtain ⟨hg, hd⟩ := lowerInductiveDeclsBare_spec hr₀
  cases hk : firstRepeatedKey (r₀.decls.toList.flatMap Ix.Kernel.Declaration.names) with
  | some k =>
    simp [hk, declined, throw, throwThe, MonadExceptOf.throw] at h
  | none =>
    simp only [hk, pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hnd := Ix.Cert.LowerDistinct.firstRepeatedKey_eq_none_iff.mp hk
    rw [hd] at hnd
    dsimp only at hnd
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Ix.Kernel.Declaration.names] at hnd
    exact ⟨hg, hd, hnd⟩

theorem readInductiveBare_generated_zero {md : Mode} {cx : Ctx md} {owner : _root_.Address}
    {c : Ixon.Constant} {ms : Array Ixon.MutConst} {r : Read md}
    (h : readInductiveBare cx owner c ms = .ok r) :
    r.generated = 0 := by
  unfold readInductiveBare at h
  split at h
  · dsimp only at h
    rcases ite_ok h with h | h
    · split at h
      · rcases ite_ok h with h | h
        · exact (fail_bind h).elim
        · rcases ite_ok h with h | h
          · obtain ⟨_, -, h⟩ := except_bind_ok.mp h
            obtain ⟨_, -, h⟩ := except_bind_ok.mp h
            obtain ⟨_, -, h⟩ := except_bind_ok.mp h
            exact (lowerInductiveBare_spec h).1
          · exact (fail_bind h).elim
      · exact (throw_ok h).elim
    · exact (fail_bind h).elim
  · exact (throw_ok h).elim

theorem readRecord_generated_zero_of_no_generated {md : Mode} {cx : Ctx md} {st : State md}
    {owner : _root_.Address} {c : Ixon.Constant} {r : Read md}
    (h : readRecord cx st owner c = .ok r)
    (hno : ∀ d ∈ r.decls.toList, d.isGenerated = false) :
    r.generated = 0 := by
  rcases Ix.Cert.ReaderUnits.readRecord_lowering h with ⟨hg, _⟩ | ⟨gens, suffix, hd, hg, _⟩
  · exact hg
  · cases gens with
    | nil => simpa using hg
    | cons g gs =>
      have htake : g ∈ r.decls.toList.take r.generated := by
        rw [hd, hg, List.take_left]
        exact List.mem_cons_self
      have ht := Ix.Cert.EvidenceTransfer.readRecord_generated h g htake
      have hf := hno g (by rw [hd]; exact List.mem_append_left _ List.mem_cons_self)
      rw [ht] at hf
      cases hf

theorem readRecordBare_generated_zero {md : Mode} {cx : Ctx md} {st : State md}
    {owner : _root_.Address} {c : Ixon.Constant} {r : Read md}
    (h : readRecordBare cx st owner c = .ok r) :
    r.generated = 0 := by
  unfold readRecordBare at h
  cases hinfo : c.info with
  | muts ms =>
    simp only [hinfo] at h
    split at h
    · rcases ite_ok h with h | h
      · exact (fail_bind h).elim
      · obtain ⟨rInd, hrInd, h⟩ := except_bind_ok.mp h
        exact (finishInductiveRead_data h).1.trans (readInductiveBare_generated_zero hrInd)
    · rename_i hind
      unfold readRecord at h
      simp only [hinfo] at h
      split at h
      · rename_i hind'
        exact absurd hind' hind
      · rcases ite_ok h with h | h
        · rcases ite_ok h with h | h
          · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
          · obtain ⟨_, -, h⟩ := except_bind_ok.mp h
            exact (Ix.Cert.ReaderUnits.lowerTwin_spec h).1
        · rcases ite_ok h with h | h
          · split at h
            · exact (fail_bind h).elim
            · split at h
              · obtain ⟨_, -, h⟩ := except_bind_ok.mp h
                simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
              · exact (throw_ok h).elim
          · exact (throw_ok h).elim
  | dPrj _ | iPrj _ | rPrj _ | cPrj _ =>
    simp only [hinfo] at h
    unfold readRecord at h; simp only [hinfo] at h
    rcases ite_ok h with h | h
    · exact (fail_bind h).elim
    · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | defn _ =>
    simp only [hinfo] at h
    unfold readRecord at h; simp only [hinfo] at h
    obtain ⟨_, -, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | recr _ =>
    simp only [hinfo] at h
    unfold readRecord at h; simp only [hinfo] at h
    rcases ite_ok h with h | h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
    · split at h
      · exact (Ix.Cert.ReaderUnits.lowerTwin_spec h).1
      · exact (throw_ok h).elim
  | axio _ =>
    simp only [hinfo] at h
    unfold readRecord at h; simp only [hinfo] at h
    rcases ite_ok h with h | h
    · exact (fail_bind h).elim
    · obtain ⟨_, -, h⟩ := except_bind_ok.mp h
      obtain ⟨_, -, h⟩ := except_bind_ok.mp h
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | quot _ =>
    simp only [hinfo] at h
    unfold readRecord at h; simp only [hinfo] at h
    obtain ⟨_, -, h⟩ := except_bind_ok.mp h
    obtain ⟨_, -, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl

theorem preludeFor_decls_not_generated {md : Mode} {t : Ix.Kernel.RoleTable} {pre : Prelude md}
    (hpre : preludeFor t = .ok pre) :
    ∀ d ∈ pre.ix.decls.toList, d.isGenerated = false := by
  have hshape := preludeFor_shape hpre
  intro d hd
  have hnames_mem : d.names ∈ pre.ix.decls.toList.map (·.names) :=
    List.mem_map.mpr ⟨d, hd, rfl⟩
  rw [hshape] at hnames_mem
  obtain ⟨roles, hroles_mem, hnames_eq⟩ := List.mem_map.mp hnames_mem
  unfold Ix.Kernel.Declaration.isGenerated
  rw [← hnames_eq]
  cases roles with
  | nil => simp
  | cons r rs =>
    simp [Ix.Kernel.Key.isAux]

theorem streamRead_projLevels_empty_of_no_generated {md : Mode} {cx : Ctx md}
    {st st' : State md} {records : List (_root_.Address × Ixon.Constant)} {out : Array (CDecl md)}
    (h : StreamRead cx st records st' out)
    (hemp : ∀ k : CName md, st.projLevels[k]? = none)
    (hno : ∀ d ∈ out.toList, d.isGenerated = false) :
    ∀ k : CName md, st'.projLevels[k]? = none := by
  induction h with
  | nil => exact hemp
  | @cons st₀ _ _ _ r _ tailOut read _ ih =>
    have hno_r : ∀ d ∈ r.decls.toList, d.isGenerated = false := fun d hd =>
      hno d (by rw [Array.toList_append]; exact List.mem_append_left _ hd)
    have hno_tail : ∀ d ∈ tailOut.toList, d.isGenerated = false := fun d hd =>
      hno d (by rw [Array.toList_append]; exact List.mem_append_right _ hd)
    have hg := readRecord_generated_zero_of_no_generated read hno_r
    have hemp' : ∀ k : CName md, (st₀.commit r).projLevels[k]? = none := by
      intro k
      rw [projLevels_commit_of_generated_zero st₀ hg]
      exact hemp k
    exact ih hemp' hno_tail

/-- Unpack `preludeRead t = .ok pre` without unfolding `RoleData`. -/
theorem preludeRead_unpack {md : Mode} {t : Ix.Kernel.RoleTable} {pre : Prelude md}
    (h : preludeRead t = .ok pre) :
    ∃ rs extra extraBlobs,
      readRecords (contextOf t rs [] extra extraBlobs) {} rs = .ok (pre.state, pre.ix.decls) := by
  unfold preludeRead at h
  generalize preludeRecords = pr at h
  generalize evidenceRecords = er at h
  generalize evidenceBlobs = eb at h
  cases pr with
  | error e => simp [bind, Except.bind] at h
  | ok rs =>
    cases er with
    | error e => simp [bind, Except.bind] at h
    | ok extra =>
      cases eb with
      | error e => simp [bind, Except.bind] at h
      | ok extraBlobs =>
        simp only [bind, Except.bind] at h
        unfold readPrelude at h
        dsimp only at h
        split at h
        · rename_i st decls hrr
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          exact ⟨rs, extra, extraBlobs, hrr⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `pre.state.projLevels` is empty for every `preludeFor t = .ok pre`. -/
theorem preludeFor_projLevels_empty {md : Mode} {t : Ix.Kernel.RoleTable} {pre : Prelude md}
    (hpre : preludeFor t = .ok pre) :
    ∀ k : CName md, pre.state.projLevels[k]? = none := by
  obtain ⟨rs, extra, extraBlobs, hrr⟩ := preludeRead_unpack (preludeFor_checks hpre).1
  exact streamRead_projLevels_empty_of_no_generated (readRecords_spec hrr)
    (fun _ => by simp) (preludeFor_decls_not_generated hpre)

/-- Along any `StreamReadBare`, `projLevels` remains empty at every intermediate and final state. -/
theorem streamReadBare_projLevels_empty {md : Mode} {cx : Ctx md}
    {st st' : State md} {records : List (_root_.Address × Ixon.Constant)} {out : Array (CDecl md)}
    (h : StreamReadBare cx st records st' out)
    (hemp : ∀ k : CName md, st.projLevels[k]? = none) :
    ∀ k : CName md, st'.projLevels[k]? = none := by
  induction h with
  | nil => exact hemp
  | @cons st₀ _ _ _ r _ _ read _ ih =>
    have hg := readRecordBare_generated_zero read
    refine ih fun k => ?_
    rw [projLevels_commit_of_generated_zero st₀ hg]
    exact hemp k

/-! ## Structural `DeclNonAux` (`NonAuxKey`, `RefsIn NonAuxKey`, distinct install names) -/

/-- A key that is not derived (`Key.aux`), i.e., `.id` or `.role`. -/
def NonAuxKey {md : Mode} (k : Ix.Kernel.Key md) : Prop :=
  ∀ b s, k ≠ .aux b s

theorem isAux_eq_false_iff {md : Mode} {k : Ix.Kernel.Key md} :
    k.isAux = false ↔ NonAuxKey k := by
  cases k <;> simp [Ix.Kernel.Key.isAux, NonAuxKey]

/-- Structural non-aux property of a `ConstantInfo`. -/
def ConstantInfoNonAux {md : Mode} (ci : Ix.Kernel.ConstantInfo md) : Prop :=
  NonAuxKey ci.name ∧
  ci.toConstantVal.type.RefsIn NonAuxKey ∧
  (match ci with
    | .defnInfo _ v _ => v.RefsIn NonAuxKey
    | .thmInfo _ v => v.RefsIn NonAuxKey
    | .recInfo _ _ _ rules => ∀ rl ∈ rules, NonAuxKey rl.ctor ∧ rl.rhs.RefsIn NonAuxKey
    | _ => True)

/-- Every constant in `IxVM.Consistency.installs d` is `ConstantInfoNonAux`, and the names of
`IxVM.Consistency.installs d` are pairwise distinct. -/
def DeclNonAux (d : Ix.Kernel.Declaration .anon) : Prop :=
  (∀ ci₀ ∈ IxVM.Consistency.installs d, ConstantInfoNonAux ci₀) ∧
  ((IxVM.Consistency.installs d).map (·.name)).Nodup

/-- Boolean mirror of `Expr.RefsIn NonAuxKey`. -/
def exprNonAuxB {md : Mode} : Ix.Kernel.Expr md → Bool
  | .bvar _ => true
  | .fvar _ _ => true
  | .sort _ => true
  | .const n _ => !n.isAux
  | .app f a => exprNonAuxB f && exprNonAuxB a
  | .lam ty b _ => exprNonAuxB ty && exprNonAuxB b
  | .forallE ty b _ => exprNonAuxB ty && exprNonAuxB b
  | .letE ty v b _ => exprNonAuxB ty && exprNonAuxB v && exprNonAuxB b
  | .lit _ => true
  | .proj _ _ e => exprNonAuxB e

theorem exprNonAuxB_eq_true_iff {md : Mode} :
    ∀ e : Ix.Kernel.Expr md, exprNonAuxB e = true ↔ e.RefsIn NonAuxKey
  | .bvar _ | .fvar _ _ | .sort _ | .lit _ => by simp [exprNonAuxB, Ix.Kernel.Expr.RefsIn]
  | .const n _ => by
    simp [exprNonAuxB, Ix.Kernel.Expr.RefsIn, isAux_eq_false_iff]
  | .app f a => by
    simp [exprNonAuxB, Ix.Kernel.Expr.RefsIn, Bool.and_eq_true,
      exprNonAuxB_eq_true_iff f, exprNonAuxB_eq_true_iff a]
  | .lam ty b _ => by
    simp [exprNonAuxB, Ix.Kernel.Expr.RefsIn, Bool.and_eq_true,
      exprNonAuxB_eq_true_iff ty, exprNonAuxB_eq_true_iff b]
  | .forallE ty b _ => by
    simp [exprNonAuxB, Ix.Kernel.Expr.RefsIn, Bool.and_eq_true,
      exprNonAuxB_eq_true_iff ty, exprNonAuxB_eq_true_iff b]
  | .letE ty v b _ => by
    simp [exprNonAuxB, Ix.Kernel.Expr.RefsIn, Bool.and_eq_true, and_assoc,
      exprNonAuxB_eq_true_iff ty, exprNonAuxB_eq_true_iff v, exprNonAuxB_eq_true_iff b]
  | .proj _ _ e => by
    simp [exprNonAuxB, Ix.Kernel.Expr.RefsIn, exprNonAuxB_eq_true_iff e]

/-- Boolean mirror of `ConstantInfoNonAux`. -/
def cinfoNonAuxB {md : Mode} (ci : Ix.Kernel.ConstantInfo md) : Bool :=
  !ci.name.isAux &&
  exprNonAuxB ci.toConstantVal.type &&
  match ci with
  | .defnInfo _ v _ => exprNonAuxB v
  | .thmInfo _ v => exprNonAuxB v
  | .recInfo _ _ _ rules => rules.all fun rl => !rl.ctor.isAux && exprNonAuxB rl.rhs
  | _ => true

theorem cinfoNonAuxB_eq_true_iff {md : Mode} (ci : Ix.Kernel.ConstantInfo md) :
    cinfoNonAuxB ci = true ↔ ConstantInfoNonAux ci := by
  cases ci <;>
    simp [cinfoNonAuxB, ConstantInfoNonAux, Bool.and_eq_true,
      isAux_eq_false_iff, exprNonAuxB_eq_true_iff, List.all_eq_true, and_assoc]

theorem basisDeclsA_nonAux (kind : Ix.Kernel.BasisKind) :
    ∀ ci₀ ∈ (kind.declsA : List (Ix.Kernel.ConstantInfo .anon)), ConstantInfoNonAux ci₀ := by
  have hb : ((kind.declsA : List (Ix.Kernel.ConstantInfo .anon)).all cinfoNonAuxB) = true := by
    cases kind <;> decide
  intro ci₀ hmem
  exact (cinfoNonAuxB_eq_true_iff ci₀).mp (List.all_eq_true.mp hb ci₀ hmem)

theorem basisDeclsA_nodup (kind : Ix.Kernel.BasisKind) :
    (((kind.declsA : List (Ix.Kernel.ConstantInfo .anon)).map (·.name))).Nodup := by
  have hroles :
      ∃ rs : List Ix.Kernel.Role,
        ((kind.declsA : List (Ix.Kernel.ConstantInfo .anon)).map (·.name)) =
          rs.map Ix.Kernel.Key.role ∧ rs.Nodup := by
    cases kind with
    | eqK => exact ⟨[.eq, .eqRefl, .eqRec], rfl, by decide⟩
    | natK => exact ⟨[.nat, .natZero, .natSucc, .natRec], rfl, by decide⟩
    | punitK => exact ⟨[.punit, .punitUnit, .punitRec], rfl, by decide⟩
    | emptyK => exact ⟨[.empty, .emptyRec], rfl, by decide⟩
    | falseK => exact ⟨[.false, .falseRec], rfl, by decide⟩
    | quotK => exact ⟨[.quot, .quotMk, .quotLift, .quotInd, .quotSound], rfl, by decide⟩
  obtain ⟨rs, heq, hnd⟩ := hroles
  rw [heq]
  exact hnd.map fun _ _ h => by injection h

theorem declNonAux_axiomDecl {cv : Ix.Kernel.ConstantVal .anon}
    (hname : NonAuxKey cv.name) (hty : cv.type.RefsIn NonAuxKey) :
    DeclNonAux (.axiomDecl cv) := by
  unfold DeclNonAux
  simp only [IxVM.Consistency.installs]
  split
  · simp
  · refine ⟨fun ci₀ hm => ?_, by simp⟩
    rw [List.mem_singleton] at hm
    subst hm
    exact ⟨hname, hty, trivial⟩

theorem declNonAux_defnDecl {cv : Ix.Kernel.ConstantVal .anon} {v : Ix.Kernel.Expr .anon}
    {hint : Ix.Kernel.ReducibilityHint}
    (hname : NonAuxKey cv.name) (hty : cv.type.RefsIn NonAuxKey) (hv : v.RefsIn NonAuxKey) :
    DeclNonAux (.defnDecl cv v hint) := by
  refine ⟨fun ci₀ hm => ?_, by simp [IxVM.Consistency.installs]⟩
  simp only [IxVM.Consistency.installs, List.mem_singleton] at hm
  subst hm
  exact ⟨hname, hty, hv⟩

theorem declNonAux_thmDecl {cv : Ix.Kernel.ConstantVal .anon} {v : Ix.Kernel.Expr .anon}
    (hname : NonAuxKey cv.name) (hty : cv.type.RefsIn NonAuxKey) (hv : v.RefsIn NonAuxKey) :
    DeclNonAux (.thmDecl cv v) := by
  refine ⟨fun ci₀ hm => ?_, by simp [IxVM.Consistency.installs]⟩
  simp only [IxVM.Consistency.installs, List.mem_singleton] at hm
  subst hm
  exact ⟨hname, hty, hv⟩

theorem declNonAux_opaqueDecl {cv : Ix.Kernel.ConstantVal .anon} {v : Ix.Kernel.Expr .anon}
    (hname : NonAuxKey cv.name) (hty : cv.type.RefsIn NonAuxKey) :
    DeclNonAux (.opaqueDecl cv v) := by
  refine ⟨fun ci₀ hm => ?_, by simp [IxVM.Consistency.installs]⟩
  simp only [IxVM.Consistency.installs, List.mem_singleton] at hm
  subst hm
  exact ⟨hname, hty, trivial⟩

theorem declNonAux_basisDecl (kind : Ix.Kernel.BasisKind) :
    DeclNonAux (.basisDecl kind) :=
  ⟨basisDeclsA_nonAux kind, basisDeclsA_nodup kind⟩

theorem declNonAux_quotDecl (k : Ix.Kernel.QuotKind) (cv : Ix.Kernel.ConstantVal .anon) :
    DeclNonAux (.quotDecl k cv) := by
  unfold DeclNonAux
  simp only [IxVM.Consistency.installs]
  cases k with
  | type => exact ⟨basisDeclsA_nonAux .quotK, basisDeclsA_nodup .quotK⟩
  | ctor | lift | ind | sound => simp

theorem declNonAux_indDecl {block : List (Ix.Kernel.ConstantInfo .anon)} {nPd : Nat}
    (hblk : ∀ ci₀ ∈ block, ConstantInfoNonAux ci₀)
    (hnd : (block.map (·.name)).Nodup) :
    DeclNonAux (.indDecl block nPd) := by
  unfold DeclNonAux
  simp only [IxVM.Consistency.installs]
  cases Ix.Kernel.basisPinHit block with
  | some kind => exact ⟨basisDeclsA_nonAux kind, basisDeclsA_nodup kind⟩
  | none => exact ⟨hblk, hnd⟩

/-! ### Non-aux keys and expressions from `Ctx`, `convExpr`, and `MemberReader` -/

theorem contextOf_rolesKeyed {md : Mode} (t : Ix.Kernel.RoleTable)
    (records : Array (_root_.Address × Ixon.Constant)) (blobs : List (_root_.Address × ByteArray))
    (fallback : Array (_root_.Address × Ixon.Constant))
    (fallbackBlobs : List (_root_.Address × ByteArray))
    (hint : ConstRef _root_.Address → Option Ix.Kernel.ReducibilityHint)
    (reconstruct : Store → ConstRef _root_.Address → Option _root_.Address) :
    RolesKeyed (contextOf (md := md) t records blobs fallback fallbackBlobs hint reconstruct) := by
  unfold contextOf contextWith
  exact Ix.Cert.ReaderUnits.bindingsOf_keyed _ t

theorem streamContext_rolesKeyed (hash : ByteArray → _root_.Address) (t : Ix.Kernel.RoleTable)
    (pre : Prelude .anon) (constants : List (_root_.Address × Ixon.Constant))
    (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef _root_.Address → Option Ix.Kernel.ReducibilityHint) :
    RolesKeyed (Ix.Kernel.Admission.streamContext hash t pre constants blobs hint) :=
  contextOf_rolesKeyed t constants.toArray blobs (pre.records ++ pre.evidence) pre.blobs hint
    (Ix.Kernel.Admission.projectionAddress hash)

theorem memberKey_nonAux {md : Mode} {cx : Ctx md} (hrk : RolesKeyed cx)
    {ref : ConstRef _root_.Address} {k : CName md} (h : cx.memberKey ref = .ok k) :
    NonAuxKey k := by
  rcases Ix.Cert.ReaderUnits.memberKey_role_or_id hrk h with ⟨ro, rfl⟩ | ⟨i, rfl⟩ <;>
    intro _ _ hEq <;> cases hEq

theorem keyAt_nonAux {md : Mode} {cx : Ctx md} (hrk : RolesKeyed cx)
    {a : _root_.Address} {k : CName md} (h : cx.keyAt a = .ok k) :
    NonAuxKey k := by
  obtain ⟨r, -, hcases⟩ := Ctx.keyAt_ok h
  rcases hcases with hrole | ⟨-, i, -, rfl⟩
  · obtain ⟨ro, rfl⟩ := hrk r k hrole
    intro _ _ hEq; cases hEq
  · intro _ _ hEq; cases hEq

theorem convExpr_refsIn_nonAux {md : Mode} {ecx : ECx md}
    (hrk : RolesKeyed ecx.cx)
    (hself : ∀ i m k, ecx.self i = some m → m = .ok k → NonAuxKey k)
    {tbl : Array (ReadM (CExpr md))}
    (htbl : ∀ m ∈ tbl.toList, ∀ e, m = .ok e → e.RefsIn NonAuxKey) :
    ∀ (ie : Ixon.Expr) {e : CExpr md},
      convExpr ecx tbl ie = .ok e → e.RefsIn NonAuxKey
  | .var i, e, h => by
    simp only [convExpr, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [Ix.Kernel.Expr.mkBvar_eq]
    trivial
  | .sort i, e, h => by
    simp only [convExpr] at h
    obtain ⟨l, -, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    trivial
  | .ref i us, e, h => by
    simp only [convExpr] at h
    obtain ⟨k, hk, h⟩ := except_bind_ok.mp h
    obtain ⟨ls, -, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    unfold ECx.keyAt at hk
    split at hk
    · exact keyAt_nonAux hrk hk
    · exact (throw_ok hk).elim
  | .recur i us, e, h => by
    simp only [convExpr] at h
    cases hs : ecx.self i.toNat with
    | none => simp [hs, malformed, throw, throwThe, MonadExceptOf.throw] at h
    | some m =>
      simp only [hs] at h
      obtain ⟨k, hk, h⟩ := except_bind_ok.mp h
      obtain ⟨ls, -, h⟩ := except_bind_ok.mp h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact hself i.toNat m k hs hk
  | .prj i field v, e, h => by
    simp only [convExpr] at h
    obtain ⟨k, -, h⟩ := except_bind_ok.mp h
    obtain ⟨ev, hv, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Ix.Kernel.Expr.RefsIn]
    exact convExpr_refsIn_nonAux hrk hself htbl v hv
  | .str i, e, h => by
    simp only [convExpr] at h
    obtain ⟨bytes, -, h⟩ := except_bind_ok.mp h
    cases hs : String.fromUTF8? bytes with
    | none => simp [hs, malformed, throw, throwThe, MonadExceptOf.throw] at h
    | some s =>
      simp only [hs, pure, Except.pure, Except.ok.injEq] at h
      subst h
      trivial
  | .nat i, e, h => by
    simp only [convExpr] at h
    obtain ⟨n, -, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    trivial
  | .app f a, e, h => by
    simp only [convExpr] at h
    obtain ⟨ef, hf, h⟩ := except_bind_ok.mp h
    obtain ⟨ea, ha, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨convExpr_refsIn_nonAux hrk hself htbl f hf,
      convExpr_refsIn_nonAux hrk hself htbl a ha⟩
  | .lam t b, e, h => by
    simp only [convExpr] at h
    obtain ⟨et, ht, h⟩ := except_bind_ok.mp h
    obtain ⟨eb, hb, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨convExpr_refsIn_nonAux hrk hself htbl t ht,
      convExpr_refsIn_nonAux hrk hself htbl b hb⟩
  | .all t b, e, h => by
    simp only [convExpr] at h
    obtain ⟨et, ht, h⟩ := except_bind_ok.mp h
    obtain ⟨eb, hb, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨convExpr_refsIn_nonAux hrk hself htbl t ht,
      convExpr_refsIn_nonAux hrk hself htbl b hb⟩
  | .letE nonDep _ t v b, e, h => by
    simp only [convExpr] at h
    obtain ⟨et, ht, h⟩ := except_bind_ok.mp h
    obtain ⟨ev, hv, h⟩ := except_bind_ok.mp h
    obtain ⟨eb, hb, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨convExpr_refsIn_nonAux hrk hself htbl t ht,
      convExpr_refsIn_nonAux hrk hself htbl v hv,
      convExpr_refsIn_nonAux hrk hself htbl b hb⟩
  | .share i, e, h => by
    simp only [convExpr] at h
    cases hget : tbl[i.toNat]? with
    | none => simp [hget, malformed, throw, throwThe, MonadExceptOf.throw] at h
    | some r =>
      simp only [hget] at h
      exact htbl r (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hget)) e h

theorem memberReader_read_refsIn_nonAux {md : Mode} {cx : Ctx md} (hrk : RolesKeyed cx)
    {src : Ixon.Constant} {param : Nat → Ix.Kernel.LevelParam}
    {self : Nat → Option (ReadM (CName md))}
    (hself : ∀ i m k, self i = some m → m = .ok k → NonAuxKey k)
    {ie : Ixon.Expr} {e : CExpr md}
    (h : (MemberReader.mk' cx src param self).read ie = .ok e) :
    e.RefsIn NonAuxKey := by
  let ecx : ECx md := ⟨cx, src, src.univs.map (convUniv param), self⟩
  have htbl_fold :
      ∀ (entries : List Ixon.Expr) (tbl : Array (ReadM (CExpr md))),
        (∀ m ∈ tbl.toList, ∀ e', m = .ok e' → e'.RefsIn NonAuxKey) →
        ∀ m ∈ (entries.foldl (fun acc entry => acc.push (convExpr ecx acc entry)) tbl).toList,
          ∀ e', m = .ok e' → e'.RefsIn NonAuxKey := by
    intro entries
    induction entries with
    | nil => intro tbl hI; exact hI
    | cons entry rest ih =>
      intro tbl hI
      refine ih (tbl.push (convExpr ecx tbl entry)) fun m hm e' he' => ?_
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact hI m hm e' he'
      · exact convExpr_refsIn_nonAux hrk hself hI entry he'
  have hmk :
      (MemberReader.mk' cx src param self).ecx = ecx ∧
      (MemberReader.mk' cx src param self).tbl =
        src.sharing.toList.foldl (fun acc entry => acc.push (convExpr ecx acc entry)) #[] := by
    simp [MemberReader.mk', ecx, Array.forIn_pure_yield_eq_foldl, Array.mkEmpty,
      ← Array.foldl_toList]
  unfold MemberReader.read at h
  rw [hmk.1, hmk.2] at h
  exact convExpr_refsIn_nonAux hrk hself
    (htbl_fold src.sharing.toList #[] (fun _ hm => nomatch hm)) ie h

/-! ### `forIn` invariant in `ReadM` and per-declaration `DeclNonAux` -/

private theorem forIn_readM_inv {α σ : Type} (I : σ → Prop)
    (f : α → σ → ReadM (ForInStep σ))
    (hstep : ∀ x s r, I s → f x s = .ok r → ∃ s', r = .yield s' ∧ I s') :
    ∀ (xs : List α) {s res : σ}, I s → forIn xs s f = .ok res → I res
  | [], _, _, hI, h => by
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    rwa [← h]
  | x :: xs, s, res, hI, h => by
    rw [List.forIn_cons] at h
    obtain ⟨step, hf, h⟩ := except_bind_ok.mp h
    obtain ⟨s', rfl, hI'⟩ := hstep x s step hI hf
    exact forIn_readM_inv I f hstep xs hI' h

theorem readRecursor_nonAux {md : Mode} {cx : Ctx md} (hrk : RolesKeyed cx)
    {blockLps : List Ix.Kernel.LevelParam} {ref : ConstRef _root_.Address} {entry : RecEntry}
    {res : CVal md × RecCounts × List (Ix.Kernel.RecRule md)}
    (h : readRecursor cx blockLps ref entry = .ok res) :
    NonAuxKey res.1.name ∧
    res.1.type.RefsIn NonAuxKey ∧
    ∀ rl ∈ res.2.2, NonAuxKey rl.ctor ∧ rl.rhs.RefsIn NonAuxKey := by
  unfold readRecursor at h
  split at h
  · rename_i rOwner j
    split at h
    · rename_i rc _
      split at h
      · rcases ite_ok h with h | h
        · exact (fail_bind h).elim
        · obtain ⟨key, hkey, h⟩ := except_bind_ok.mp h
          have hk_na : NonAuxKey key := memberKey_nonAux hrk hkey
          have hrself : ∀ i m k,
              (match rc.info with
                | .muts rms =>
                  if i < rms.size then some (cx.memberKey (.member rOwner i)) else none
                | _ => if i == 0 then some (pure key) else none) = some m →
              m = .ok k → NonAuxKey k := by
            intro i m k hs hm
            cases hrc : rc.info with
            | muts rms =>
              simp only [hrc] at hs
              split at hs
              · injection hs with hs; rw [← hs] at hm; exact memberKey_nonAux hrk hm
              · cases hs
            | _ =>
              simp only [hrc] at hs
              split at hs
              · injection hs with hs
                rw [← hs] at hm
                simp only [pure, Except.pure, Except.ok.injEq] at hm
                rwa [← hm]
              · cases hs
          obtain ⟨ty, hty, h⟩ := except_bind_ok.mp h
          have hty_na := memberReader_read_refsIn_nonAux hrk hrself hty
          split at h
          · rcases ite_ok h with h | h
            · split at h
              · obtain ⟨rules, hrules, h⟩ := except_bind_ok.mp h
                simp only [pure, Except.pure, Except.ok.injEq] at h
                subst h
                rw [← Array.forIn_toList] at hrules
                have hrl_na := forIn_readM_inv
                  (fun (acc : List (Ix.Kernel.RecRule md)) =>
                    ∀ rl ∈ acc, NonAuxKey rl.ctor ∧ rl.rhs.RefsIn NonAuxKey)
                  _
                  (fun ⟨rule, idx⟩ acc q hI hq => by
                    obtain ⟨ckey, hckey, hq⟩ := except_bind_ok.mp hq
                    obtain ⟨rhs, hrhs, hq⟩ := except_bind_ok.mp hq
                    simp only [pure, Except.pure, Except.ok.injEq] at hq
                    subst hq
                    refine ⟨_, rfl, fun rl hrl => ?_⟩
                    rcases List.mem_append.mp hrl with hrl | hrl
                    · exact hI rl hrl
                    · rw [List.mem_singleton] at hrl
                      subst hrl
                      exact ⟨memberKey_nonAux hrk hckey,
                        memberReader_read_refsIn_nonAux hrk hrself hrhs⟩)
                  _ (by simp) hrules
                exact ⟨hk_na, hty_na, hrl_na⟩
              · exact (throw_ok h).elim
            · exact (fail_bind h).elim
          · exact (throw_ok h).elim
      · exact (throw_ok h).elim
    · exact (throw_ok h).elim
  · exact (throw_ok h).elim

theorem lowerTwin_declNonAux {cx : Ctx .anon} (hrk : RolesKeyed cx)
    {twins : Array (ConstRef _root_.Address × RecEntry)} {r : Read .anon}
    (h : lowerTwin cx twins = .ok r) :
    ∀ d ∈ r.decls.toList, DeclNonAux d := by
  unfold lowerTwin at h
  split at h
  · dsimp only at h
    rcases ite_ok h with h | h
    · split at h
      · split at h
        · split at h
          · rcases ite_ok h with h | h
            · split at h
              · rcases ite_ok h with h | h
                · exact (fail_bind h).elim
                · rcases ite_ok h with h | h
                  · obtain ⟨_, -, h⟩ := except_bind_ok.mp h
                    obtain ⟨recs, hrecs, h⟩ := except_bind_ok.mp h
                    rw [← Array.forIn_toList] at hrecs
                    have hr_na := forIn_readM_inv
                      (fun (acc : Array (CVal .anon × RecCounts × List (Ix.Kernel.RecRule .anon))) =>
                        ∀ e ∈ acc.toList,
                          NonAuxKey e.1.name ∧ e.1.type.RefsIn NonAuxKey ∧
                          ∀ rl ∈ e.2.2, NonAuxKey rl.ctor ∧ rl.rhs.RefsIn NonAuxKey)
                      _
                      (fun _ acc q hI hq => by
                        obtain ⟨rv, hrv, hq⟩ := except_bind_ok.mp hq
                        simp only [pure, Except.pure, Except.ok.injEq] at hq
                        subst hq
                        refine ⟨_, rfl, fun e he => ?_⟩
                        rw [Array.toList_push, List.mem_append, List.mem_singleton] at he
                        rcases he with he | rfl
                        · exact hI e he
                        · exact readRecursor_nonAux hrk hrv)
                      _ (by simp) hrecs
                    simp only [ite_not, bne_iff_ne, ne_eq] at h
                    split at h
                    all_goals
                      rcases ite_ok h with h | h
                      all_goals obtain ⟨_, -, h⟩ := except_bind_ok.mp h
                      all_goals
                        cases hk : firstRepeatedKey
                            ((recs.toList.map fun x =>
                              Ix.Kernel.ConstantInfo.recInfo x.1
                                (x.2.1.params + x.2.1.motives + x.2.1.minors + x.2.1.indices)
                                (x.2.1.params + x.2.1.motives + x.2.1.minors) x.2.2).map (·.name)) with
                        | some dup =>
                          rw [hk] at h
                          exact (fail_bind h).elim
                        | none =>
                          simp only [hk, pure, Except.pure, Except.ok.injEq] at h
                          subst h
                          intro d hd
                          simp at hd
                          subst hd
                          refine declNonAux_indDecl (fun ci₀ hci => ?_)
                            (Ix.Cert.LowerDistinct.firstRepeatedKey_eq_none_iff.mp hk)
                          obtain ⟨e, hm, rfl⟩ := List.mem_map.mp hci
                          exact hr_na e hm
                  · exact (fail_bind h).elim
              · exact (throw_ok h).elim
            · exact (fail_bind h).elim
          · exact (throw_ok h).elim
        · exact (throw_ok h).elim
      · exact (throw_ok h).elim
    · exact (fail_bind h).elim
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro _ hd
    simp at hd

/-- Non-aux invariant on a parsed `BlockRead .anon`. -/
def BlockReadNonAux (rb : BlockRead .anon) : Prop :=
  (∀ e ∈ rb.types.toList, NonAuxKey e.1.name ∧ e.1.type.RefsIn NonAuxKey) ∧
  (∀ e ∈ rb.ctors.toList, NonAuxKey e.1.name ∧ e.1.type.RefsIn NonAuxKey) ∧
  (∀ e ∈ rb.recs.toList, NonAuxKey e.1.name ∧ e.1.type.RefsIn NonAuxKey ∧
    ∀ rl ∈ e.2.2, NonAuxKey rl.ctor ∧ rl.rhs.RefsIn NonAuxKey)

theorem blockReadNonAux_block {rb : BlockRead .anon} (h : BlockReadNonAux rb) :
    ∀ ci₀ ∈
      (rb.types.toList.map fun x => Ix.Kernel.ConstantInfo.indInfo x.1 {}) ++
      (rb.ctors.toList.map fun x => Ix.Kernel.ConstantInfo.ctorInfo x.1 x.2.1 x.2.2) ++
      (rb.recs.toList.map fun x =>
        Ix.Kernel.ConstantInfo.recInfo x.1
          (x.2.1.params + x.2.1.motives + x.2.1.minors + x.2.1.indices)
          (x.2.1.params + x.2.1.motives + x.2.1.minors) x.2.2),
      ConstantInfoNonAux ci₀ := by
  intro ci₀ hci
  simp only [List.mem_append, List.mem_map] at hci
  rcases hci with (⟨e, hm, rfl⟩ | ⟨e, hm, rfl⟩) | ⟨e, hm, rfl⟩
  · obtain ⟨hn, hty⟩ := h.1 _ hm
    exact ⟨hn, hty, trivial⟩
  · obtain ⟨hn, hty⟩ := h.2.1 _ hm
    exact ⟨hn, hty, trivial⟩
  · exact h.2.2 _ hm

theorem readInductiveBare_declNonAux {cx : Ctx .anon} (hrk : RolesKeyed cx)
    {owner : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst} {r : Read .anon}
    (h : readInductiveBare cx owner c ms = .ok r) :
    ∀ d ∈ r.decls.toList, DeclNonAux d := by
  unfold readInductiveBare at h
  split at h
  · dsimp only at h
    rcases ite_ok h with h | h
    · split at h
      · rcases ite_ok h with h | h
        · exact (fail_bind h).elim
        · rcases ite_ok h with h | h
          · have hself : ∀ i m k,
                (if i < ms.size then some (cx.memberKey (.member owner i)) else none) = some m →
                m = .ok k → NonAuxKey k := by
              intro i m k hs hm
              split at hs
              · injection hs with hs; rw [← hs] at hm; exact memberKey_nonAux hrk hm
              · cases hs
            obtain ⟨types, htypes, h⟩ := except_bind_ok.mp h
            rw [← Array.forIn_toList] at htypes
            have hty_na := forIn_readM_inv
              (fun (acc : Array (CVal .anon × Nat × Nat)) =>
                ∀ e ∈ acc.toList, NonAuxKey e.1.name ∧ e.1.type.RefsIn NonAuxKey)
              _
              (fun _ acc q hI hq => by
                obtain ⟨k, hk, hq⟩ := except_bind_ok.mp hq
                obtain ⟨ty, hty, hq⟩ := except_bind_ok.mp hq
                simp only [pure, Except.pure, Except.ok.injEq] at hq
                subst hq
                refine ⟨_, rfl, fun e he => ?_⟩
                rw [Array.toList_push, List.mem_append, List.mem_singleton] at he
                rcases he with he | rfl
                · exact hI e he
                · exact ⟨memberKey_nonAux hrk hk,
                    memberReader_read_refsIn_nonAux hrk hself hty⟩)
              _ (by simp) htypes
            obtain ⟨cs, hcs, h⟩ := except_bind_ok.mp h
            rw [← Array.forIn_toList] at hcs
            have hct_na := forIn_readM_inv
              (fun s => ∀ e ∈ s.1.toList, NonAuxKey e.1.name ∧ e.1.type.RefsIn NonAuxKey)
              _
              (fun _ acc q hI hq => by
                obtain ⟨s1, hs1, hq⟩ := except_bind_ok.mp hq
                simp only [pure, Except.pure, Except.ok.injEq] at hq
                subst hq
                rw [← Array.forIn_toList] at hs1
                refine ⟨_, rfl, ?_⟩
                exact forIn_readM_inv
                  (fun t => ∀ e ∈ t.1.toList, NonAuxKey e.1.name ∧ e.1.type.RefsIn NonAuxKey)
                  _
                  (fun _ t r' hIt hr' => by
                    rcases ite_ok hr' with hr' | hr'
                    · rcases ite_ok hr' with hr' | hr'
                      · exact (fail_bind hr').elim
                      · obtain ⟨k, hk, hr'⟩ := except_bind_ok.mp hr'
                        obtain ⟨ty, hty, hr'⟩ := except_bind_ok.mp hr'
                        rcases ite_ok hr' with hr' | hr'
                        · simp only [pure, Except.pure, Except.ok.injEq] at hr'
                          subst hr'
                          refine ⟨_, rfl, fun e he => ?_⟩
                          rw [Array.toList_push, List.mem_append, List.mem_singleton] at he
                          rcases he with he | rfl
                          · exact hIt e he
                          · exact ⟨memberKey_nonAux hrk hk,
                              memberReader_read_refsIn_nonAux hrk hself hty⟩
                        · exact (fail_bind hr').elim
                    · exact (fail_bind hr').elim)
                  _ hI hs1)
              _ (by simp) hcs
            obtain ⟨recs, hrecs, h⟩ := except_bind_ok.mp h
            rw [← Array.forIn_toList] at hrecs
            have hrc_na := forIn_readM_inv
              (fun (acc : Array (CVal .anon × RecCounts × List (Ix.Kernel.RecRule .anon))) =>
                ∀ e ∈ acc.toList,
                  NonAuxKey e.1.name ∧ e.1.type.RefsIn NonAuxKey ∧
                  ∀ rl ∈ e.2.2, NonAuxKey rl.ctor ∧ rl.rhs.RefsIn NonAuxKey)
              _
              (fun _ acc q hI hq => by
                split at hq
                · obtain ⟨rv, hrv, hq⟩ := except_bind_ok.mp hq
                  simp only [pure, Except.pure, Except.ok.injEq] at hq
                  subst hq
                  refine ⟨_, rfl, fun e he => ?_⟩
                  rw [Array.toList_push, List.mem_append, List.mem_singleton] at he
                  rcases he with he | rfl
                  · exact hI e he
                  · exact readRecursor_nonAux hrk hrv
                · exact (throw_ok hq).elim)
              _ (by simp) hrecs
            obtain ⟨_, hd, hnd⟩ := lowerInductiveBare_spec h
            rw [hd]
            intro d hd'
            dsimp only at hd'
            rcases List.mem_singleton.mp hd' with rfl
            exact declNonAux_indDecl
              (blockReadNonAux_block (rb := ⟨0, types, cs.1, #[], recs⟩) ⟨hty_na, hct_na, hrc_na⟩)
              hnd
          · exact (fail_bind h).elim
      · exact (throw_ok h).elim
    · exact (fail_bind h).elim
  · exact (throw_ok h).elim

theorem readInductive_noGen_declNonAux {cx : Ctx .anon} (hrk : RolesKeyed cx) {st : State .anon}
    {owner : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst} {r : Read .anon}
    (h : readInductive cx st owner c ms = .ok r) (hg : r.generated = 0) :
    ∀ d ∈ r.decls.toList, DeclNonAux d := by
  unfold readInductive at h
  split at h
  · dsimp only at h
    rcases ite_ok h with h | h
    · split at h
      · rcases ite_ok h with h | h
        · exact (fail_bind h).elim
        · rcases ite_ok h with h | h
          · have hself : ∀ i m k,
                (if i < ms.size then some (cx.memberKey (.member owner i)) else none) = some m →
                m = .ok k → NonAuxKey k := by
              intro i m k hs hm
              split at hs
              · injection hs with hs; rw [← hs] at hm; exact memberKey_nonAux hrk hm
              · cases hs
            obtain ⟨types, htypes, h⟩ := except_bind_ok.mp h
            rw [← Array.forIn_toList] at htypes
            have hty_na := forIn_readM_inv
              (fun (acc : Array (CVal .anon × Nat × Nat)) =>
                ∀ e ∈ acc.toList, NonAuxKey e.1.name ∧ e.1.type.RefsIn NonAuxKey)
              _
              (fun _ acc q hI hq => by
                obtain ⟨k, hk, hq⟩ := except_bind_ok.mp hq
                obtain ⟨ty, hty, hq⟩ := except_bind_ok.mp hq
                simp only [pure, Except.pure, Except.ok.injEq] at hq
                subst hq
                refine ⟨_, rfl, fun e he => ?_⟩
                rw [Array.toList_push, List.mem_append, List.mem_singleton] at he
                rcases he with he | rfl
                · exact hI e he
                · exact ⟨memberKey_nonAux hrk hk,
                    memberReader_read_refsIn_nonAux hrk hself hty⟩)
              _ (by simp) htypes
            obtain ⟨cs, hcs, h⟩ := except_bind_ok.mp h
            rw [← Array.forIn_toList] at hcs
            have hct_na := forIn_readM_inv
              (fun s => ∀ e ∈ s.1.toList, NonAuxKey e.1.name ∧ e.1.type.RefsIn NonAuxKey)
              _
              (fun _ acc q hI hq => by
                obtain ⟨s1, hs1, hq⟩ := except_bind_ok.mp hq
                simp only [pure, Except.pure, Except.ok.injEq] at hq
                subst hq
                rw [← Array.forIn_toList] at hs1
                refine ⟨_, rfl, ?_⟩
                exact forIn_readM_inv
                  (fun t => ∀ e ∈ t.1.toList, NonAuxKey e.1.name ∧ e.1.type.RefsIn NonAuxKey)
                  _
                  (fun _ t r' hIt hr' => by
                    rcases ite_ok hr' with hr' | hr'
                    · rcases ite_ok hr' with hr' | hr'
                      · exact (fail_bind hr').elim
                      · obtain ⟨k, hk, hr'⟩ := except_bind_ok.mp hr'
                        obtain ⟨ty, hty, hr'⟩ := except_bind_ok.mp hr'
                        rcases ite_ok hr' with hr' | hr'
                        · simp only [pure, Except.pure, Except.ok.injEq] at hr'
                          subst hr'
                          refine ⟨_, rfl, fun e he => ?_⟩
                          rw [Array.toList_push, List.mem_append, List.mem_singleton] at he
                          rcases he with he | rfl
                          · exact hIt e he
                          · exact ⟨memberKey_nonAux hrk hk,
                              memberReader_read_refsIn_nonAux hrk hself hty⟩
                        · exact (fail_bind hr').elim
                    · exact (fail_bind hr').elim)
                  _ hI hs1)
              _ (by simp) hcs
            obtain ⟨recs, hrecs, h⟩ := except_bind_ok.mp h
            rw [← Array.forIn_toList] at hrecs
            have hrc_na := forIn_readM_inv
              (fun (acc : Array (CVal .anon × RecCounts × List (Ix.Kernel.RecRule .anon))) =>
                ∀ e ∈ acc.toList,
                  NonAuxKey e.1.name ∧ e.1.type.RefsIn NonAuxKey ∧
                  ∀ rl ∈ e.2.2, NonAuxKey rl.ctor ∧ rl.rhs.RefsIn NonAuxKey)
              _
              (fun _ acc q hI hq => by
                split at hq
                · obtain ⟨rv, hrv, hq⟩ := except_bind_ok.mp hq
                  simp only [pure, Except.pure, Except.ok.injEq] at hq
                  subst hq
                  refine ⟨_, rfl, fun e he => ?_⟩
                  rw [Array.toList_push, List.mem_append, List.mem_singleton] at he
                  rcases he with he | rfl
                  · exact hI e he
                  · exact readRecursor_nonAux hrk hrv
                · exact (throw_ok hq).elim)
              _ (by simp) hrecs
            have hnd_all := Ix.Cert.LowerDistinct.lowerInductive_names_nodup h
            have hdecls := Ix.Cert.LowerDistinct.lowerInductiveDecls_of_ok h
            unfold lowerInductiveDecls at hdecls
            simp only [ite_not, bne_iff_ne, ne_eq] at hdecls
            split at hdecls
            all_goals
              rcases ite_ok hdecls with hdecls | hdecls
              all_goals obtain ⟨_, -, hdecls⟩ := except_bind_ok.mp hdecls
              all_goals
                rcases ite_ok hdecls with hdecls | hdecls
                · split at hdecls
                  · simp [declined, throw, throwThe, MonadExceptOf.throw] at hdecls
                  · rename_i gen _
                    simp only [pure, Except.pure, Except.ok.injEq] at hdecls
                    subst hdecls
                    cases gen with
                    | nil =>
                      rw [Array.toList_push, List.toList_toArray, List.nil_append] at hnd_all
                      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
                        Ix.Kernel.Declaration.names] at hnd_all
                      intro d hd'
                      rw [Array.toList_push, List.toList_toArray, List.nil_append] at hd'
                      rcases List.mem_singleton.mp hd' with rfl
                      exact declNonAux_indDecl
                        (blockReadNonAux_block (rb := ⟨0, types, cs.1, #[], recs⟩)
                          ⟨hty_na, hct_na, hrc_na⟩)
                        hnd_all
                    | cons _ _ => simp at hg
                · simp only [pure, Except.pure, Except.ok.injEq] at hdecls
                  subst hdecls
                  dsimp only at hnd_all
                  simp only [List.flatMap_cons, List.flatMap_nil,
                    List.append_nil, Ix.Kernel.Declaration.names] at hnd_all
                  intro d hd'
                  dsimp only at hd'
                  rcases List.mem_singleton.mp hd' with rfl
                  exact declNonAux_indDecl
                    (blockReadNonAux_block (rb := ⟨0, types, cs.1, #[], recs⟩)
                      ⟨hty_na, hct_na, hrc_na⟩)
                    hnd_all
          · exact (fail_bind h).elim
      · exact (throw_ok h).elim
    · exact (fail_bind h).elim
  · exact (throw_ok h).elim

theorem lowerDefinition_declNonAux {hint : Option Ix.Kernel.ReducibilityHint} {st : State .anon}
    (hemp : ∀ k : CName .anon, st.projLevels[k]? = none) {heights : CName .anon → Nat}
    {cv : CVal .anon} {value : CExpr .anon} {kind : Ix.DefKind} {safety : Ix.DefinitionSafety}
    {decl : CDecl .anon} {rw : Bool}
    (hname : NonAuxKey cv.name) (hty : cv.type.RefsIn NonAuxKey) (hv : value.RefsIn NonAuxKey)
    (h : lowerDefinition hint st heights cv value kind safety = .ok (decl, rw)) :
    DeclNonAux decl := by
  unfold lowerDefinition at h
  rw [projRewrite_eq_none hemp cv value] at h
  dsimp only at h
  split at h
  · exact (fail_bind h).elim
  · cases kind <;>
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, -⟩ := h
    · exact declNonAux_defnDecl hname hty hv
    · exact declNonAux_opaqueDecl hname hty
    · exact declNonAux_thmDecl hname hty hv

theorem readDefinition_declNonAux {cx : Ctx .anon} (hrk : RolesKeyed cx) {st : State .anon}
    (hemp : ∀ k : CName .anon, st.projLevels[k]? = none) {heights : CName .anon → Nat}
    {ref : ConstRef _root_.Address} {lps : List Ix.Kernel.LevelParam}
    {src : Ixon.Constant} {param : Nat → Ix.Kernel.LevelParam}
    {self : Nat → Option (ReadM (CName .anon))}
    (hself : ∀ i m k, self i = some m → m = .ok k → NonAuxKey k)
    {d : Ixon.Definition} {decl : CDecl .anon} {rw : Bool}
    (h : readDefinition cx st heights ref lps (MemberReader.mk' cx src param self) d =
      .ok (decl, rw)) :
    DeclNonAux decl := by
  unfold readDefinition at h
  obtain ⟨name, hname, h⟩ := except_bind_ok.mp h
  obtain ⟨ty, hty, h⟩ := except_bind_ok.mp h
  obtain ⟨val, hval, h⟩ := except_bind_ok.mp h
  exact lowerDefinition_declNonAux hemp (memberKey_nonAux hrk hname)
    (memberReader_read_refsIn_nonAux hrk hself hty)
    (memberReader_read_refsIn_nonAux hrk hself hval) h

theorem readRecord_noGen_declNonAux {cx : Ctx .anon} (hrk : RolesKeyed cx) {st : State .anon}
    (hemp : ∀ k : CName .anon, st.projLevels[k]? = none)
    {owner : _root_.Address} {c : Ixon.Constant} {r : Read .anon}
    (h : readRecord cx st owner c = .ok r) (hg : r.generated = 0) :
    ∀ d ∈ r.decls.toList, DeclNonAux d := by
  unfold readRecord at h
  cases hinfo : c.info with
  | dPrj _ | iPrj _ | rPrj _ | cPrj _ =>
    simp only [hinfo] at h
    rcases ite_ok h with h | h
    · exact (fail_bind h).elim
    · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; intro _ hd; simp at hd
  | defn defnRec =>
    simp only [hinfo] at h
    have hself : ∀ i m k,
        (if i == 0 then some (cx.memberKey (.member owner 0)) else none) = some m →
        m = .ok k → NonAuxKey k := by
      intro i m k hs hm
      split at hs
      · injection hs with hs; rw [← hs] at hm; exact memberKey_nonAux hrk hm
      · cases hs
    obtain ⟨⟨decl, rw⟩, hd, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro d hd'
    simp at hd'
    subst hd'
    exact readDefinition_declNonAux hrk hemp hself hd
  | recr _ =>
    simp only [hinfo] at h
    rcases ite_ok h with h | h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; intro _ hd; simp at hd
    · split at h
      · exact lowerTwin_declNonAux hrk h
      · exact (throw_ok h).elim
  | axio ax =>
    simp only [hinfo] at h
    rcases ite_ok h with h | h
    · exact (fail_bind h).elim
    · obtain ⟨k, hk, h⟩ := except_bind_ok.mp h
      obtain ⟨ty, hty, h⟩ := except_bind_ok.mp h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      intro d hd'
      simp at hd'
      subst hd'
      exact declNonAux_axiomDecl (memberKey_nonAux hrk hk)
        (memberReader_read_refsIn_nonAux hrk (by simp) hty)
  | quot q =>
    simp only [hinfo] at h
    obtain ⟨k, -, h⟩ := except_bind_ok.mp h
    obtain ⟨ty, -, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro d hd'
    simp at hd'
    subst hd'
    exact declNonAux_quotDecl _ _
  | muts ms =>
    simp only [hinfo] at h
    rcases ite_ok h with h | h
    · rcases ite_ok h with h | h
      · exact (fail_bind h).elim
      · obtain ⟨rInd, hrInd, h⟩ := except_bind_ok.mp h
        have hgInd := (finishInductiveRead_data h).1.symm.trans hg
        have hInd := readInductive_noGen_declNonAux hrk hrInd hgInd
        rcases finishInductiveRead_spec h with rfl | ⟨rTwin, hrTwin, rfl⟩
        · exact hInd
        · intro d hd
          rw [Array.toList_append, List.mem_append] at hd
          exact hd.elim (hInd d) (lowerTwin_declNonAux hrk hrTwin d)
    · rcases ite_ok h with h | h
      · rcases ite_ok h with h | h
        · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; intro _ hd; simp at hd
        · obtain ⟨_, -, h⟩ := except_bind_ok.mp h
          exact lowerTwin_declNonAux hrk h
      · rcases ite_ok h with h | h
        · split at h
          · exact (fail_bind h).elim
          · split at h
            · have hself : ∀ i m k,
                  (if i < ms.size then some (cx.memberKey (.member owner i)) else none) = some m →
                  m = .ok k → NonAuxKey k := by
                intro i m k hs hm
                split at hs
                · injection hs with hs; rw [← hs] at hm; exact memberKey_nonAux hrk hm
                · cases hs
              obtain ⟨s, hs, h⟩ := except_bind_ok.mp h
              simp only [pure, Except.pure, Except.ok.injEq] at h
              subst h
              rw [← Array.forIn_toList] at hs
              exact forIn_readM_inv
                (fun s => ∀ d ∈ s.2.1.toList, DeclNonAux d)
                _
                (fun _ s q hI hq => by
                  obtain ⟨⟨decl, rw⟩, hd, hq⟩ := except_bind_ok.mp hq
                  have hdecl := readDefinition_declNonAux hrk hemp hself hd
                  dsimp only at hq
                  split at hq <;> split at hq <;>
                  · simp only [pure, Except.pure, Except.ok.injEq] at hq
                    subst hq
                    refine ⟨_, rfl, fun d hd' => ?_⟩
                    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hd'
                    rcases hd' with hd' | rfl
                    · exact hI d hd'
                    · exact hdecl)
                _ (by simp) hs
            · exact (throw_ok h).elim
        · exact (throw_ok h).elim

theorem readRecordBare_declNonAux {cx : Ctx .anon} (hrk : RolesKeyed cx) {st : State .anon}
    (hemp : ∀ k : CName .anon, st.projLevels[k]? = none)
    {owner : _root_.Address} {c : Ixon.Constant} {r : Read .anon}
    (h : readRecordBare cx st owner c = .ok r) :
    ∀ d ∈ r.decls.toList, DeclNonAux d := by
  have hg := readRecordBare_generated_zero h
  unfold readRecordBare at h
  cases hinfo : c.info with
  | muts ms =>
    simp only [hinfo] at h
    split at h
    · rcases ite_ok h with h | h
      · exact (fail_bind h).elim
      · obtain ⟨rInd, hrInd, h⟩ := except_bind_ok.mp h
        have hInd := readInductiveBare_declNonAux hrk hrInd
        rcases finishInductiveRead_spec h with rfl | ⟨rTwin, hrTwin, rfl⟩
        · exact hInd
        · intro d hd
          rw [Array.toList_append, List.mem_append] at hd
          exact hd.elim (hInd d) (lowerTwin_declNonAux hrk hrTwin d)
    · exact readRecord_noGen_declNonAux hrk hemp h hg
  | _ =>
    simp only [hinfo] at h
    exact readRecord_noGen_declNonAux hrk hemp h hg

theorem preludeFor_decls_nonAux {t : Ix.Kernel.RoleTable} {pre : Prelude .anon}
    (hpre : preludeFor t = .ok pre) :
    ∀ d ∈ pre.ix.decls.toList, DeclNonAux d := by
  obtain ⟨rs, extra, extraBlobs, hrr⟩ := preludeRead_unpack (preludeFor_checks hpre).1
  have hrk : RolesKeyed (contextOf (md := .anon) t rs [] extra extraBlobs) :=
    contextOf_rolesKeyed (md := .anon) t rs [] extra extraBlobs _ _
  have hno := preludeFor_decls_not_generated hpre
  have hsr := readRecords_spec hrr
  have go : ∀ {st st' : State .anon} {recs : List (_root_.Address × Ixon.Constant)}
      {out : Array (CDecl .anon)},
      StreamRead (contextOf (md := .anon) t rs [] extra extraBlobs) st recs st' out →
      (∀ k : CName .anon, st.projLevels[k]? = none) →
      (∀ d ∈ out.toList, d.isGenerated = false) →
      ∀ d ∈ out.toList, DeclNonAux d := by
    intro st st' recs out h hemp hno_out
    induction h with
    | nil => intro _ hm; nomatch hm
    | @cons st₀ _ _ _ r _ tailOut read _ ih =>
      have hno_r : ∀ d ∈ r.decls.toList, d.isGenerated = false := fun d hd =>
        hno_out d (by rw [Array.toList_append]; exact List.mem_append_left _ hd)
      have hno_tail : ∀ d ∈ tailOut.toList, d.isGenerated = false := fun d hd =>
        hno_out d (by rw [Array.toList_append]; exact List.mem_append_right _ hd)
      have hg := readRecord_generated_zero_of_no_generated read hno_r
      have hd_r := readRecord_noGen_declNonAux hrk hemp read hg
      have hemp' : ∀ k : CName .anon, (st₀.commit r).projLevels[k]? = none := by
        intro k; rw [projLevels_commit_of_generated_zero st₀ hg]; exact hemp k
      intro d hd
      rw [Array.toList_append, List.mem_append] at hd
      exact hd.elim (hd_r d) (ih hemp' hno_tail d)
  exact go hsr (fun _ => by simp) hno

theorem streamReadBare_decls_nonAux {cx : Ctx .anon} (hrk : RolesKeyed cx)
    {st st' : State .anon} {records : List (_root_.Address × Ixon.Constant)}
    {out : Array (CDecl .anon)}
    (h : StreamReadBare cx st records st' out)
    (hemp : ∀ k : CName .anon, st.projLevels[k]? = none) :
    ∀ d ∈ out.toList, DeclNonAux d := by
  induction h with
  | nil => intro _ hm; nomatch hm
  | @cons st₀ _ _ _ r _ _ read _ ih =>
    have hg := readRecordBare_generated_zero read
    have hd_r := readRecordBare_declNonAux hrk hemp read
    have hemp' : ∀ k : CName .anon, (st₀.commit r).projLevels[k]? = none := by
      intro k; rw [projLevels_commit_of_generated_zero st₀ hg]; exact hemp k
    intro d hd
    rw [Array.toList_append, List.mem_append] at hd
    exact hd.elim (hd_r d) (ih hemp' d)

/-- **Every declaration in `preparePrelude pre.ix decls` satisfies `DeclNonAux`** whenever
`preludeFor t = .ok pre` and `decls` was read by `StreamReadBare` from `pre.state`. -/
theorem preparePrelude_declNonAux {hash : ByteArray → _root_.Address}
    {t : Ix.Kernel.RoleTable} {pre : Prelude .anon}
    {constants : List (_root_.Address × Ixon.Constant)} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef _root_.Address → Option Ix.Kernel.ReducibilityHint}
    {st' : State .anon} {decls : Array (CDecl .anon)}
    (hpre : preludeFor t = .ok pre)
    (hreads : StreamReadBare
      (Ix.Kernel.Admission.streamContext hash t pre constants blobs hint)
      pre.state constants st' decls) :
    ∀ d ∈ (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList, DeclNonAux d := by
  have hpre_na := preludeFor_decls_nonAux hpre
  have hstr_na := streamReadBare_decls_nonAux
    (streamContext_rolesKeyed hash t pre constants blobs hint)
    hreads (preludeFor_projLevels_empty hpre)
  obtain ⟨extra, hextra, hperm⟩ := Ix.Kernel.Frontend.preparePrelude_perm pre.ix decls
  intro d hd
  rcases List.mem_append.mp (hperm.mem_iff.mp hd) with hd_s | hd_e
  · exact hstr_na d hd_s
  · exact hpre_na d (hextra d hd_e)

/-! ## `AddressKey` and singleton/projection resolution helpers -/

/-- A singleton record (`defn`, `recr`, `axio`, `quot`) stored at `a` resolves to `.member a 0`. -/
theorem resolve_singleton {store : Store} {a : _root_.Address} {c : Ixon.Constant}
    (hc : store a = some c)
    (hsing : match c.info with | .defn _ | .recr _ | .axio _ | .quot _ => True | _ => False) :
    resolve store a = some (.member a 0) := by
  unfold resolve resolveSource
  rw [hc]
  cases hinfo : c.info <;> simp [hinfo] at hsing ⊢

/-- **Unconditional singleton resolution injectivity**: if `store a = some c` and `c` is not a
mutual block or projection, then ONLY `a` resolves to `.member a 0` in `store` (with zero
byte-canonicality hypothesis!). -/
theorem resolve_inj_singleton {store : Store} {a a' : _root_.Address} {c : Ixon.Constant}
    (hc : store a = some c) (hnot_muts : ∀ ms, c.info ≠ .muts ms)
    (h' : resolve store a' = some (.member a 0)) :
    a' = a := by
  unfold resolve at h'
  obtain ⟨c', _, h'⟩ := Option.bind_eq_some_iff.mp h'
  rcases Ix.Cert.ReadingKeys.resolveSource_cases h' with ⟨e, _⟩ | proj'
  · injection e with h_eq
    exact h_eq.symm
  · obtain ⟨m, hm⟩ := Ix.Cert.ReadingKeys.projectionAt_member proj'
    exact absurd hm (Ix.Cert.ReadingKeys.memberAt_block hc hnot_muts)

/-- Resolution injectivity for any reference `q` when `projectionAt store q`'s constant (if any)
is canonically hashed wherever it sits in `store`. -/
theorem resolve_inj_of_proj_authentic {store : Store} {a a' : _root_.Address}
    {q : ConstRef _root_.Address}
    (h : resolve store a = some q) (h' : resolve store a' = some q)
    (hproj : ∀ c, Ix.Cert.ReadingKeys.projectionAt store q = some c →
      (store a = some c → a = _root_.Address.admissionHash (Ixon.serConstant c)) ∧
      (store a' = some c → a' = _root_.Address.admissionHash (Ixon.serConstant c))) :
    a' = a := by
  unfold resolve at h h'
  obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c', hc', h'⟩ := Option.bind_eq_some_iff.mp h'
  rcases Ix.Cert.ReadingKeys.resolveSource_cases h with ⟨rfl, ns⟩ | proj <;>
    rcases Ix.Cert.ReadingKeys.resolveSource_cases h' with ⟨e, ns'⟩ | proj'
  · injection e with h_eq
    exact h_eq.symm
  · obtain ⟨m, hm⟩ := Ix.Cert.ReadingKeys.projectionAt_member proj'
    exact absurd hm (Ix.Cert.ReadingKeys.memberAt_block hc ns)
  · subst e
    obtain ⟨m, hm⟩ := Ix.Cert.ReadingKeys.projectionAt_member proj
    exact absurd hm (Ix.Cert.ReadingKeys.memberAt_block hc' ns')
  · have hcc' : c = c' := Option.some.inj (proj.symm.trans proj')
    subst hcc'
    obtain ⟨ha, ha'⟩ := hproj c proj
    rw [ha hc, ha' hc']

private theorem keysOf_address_isSome {md : Mode} (store : Store) (roles : Bindings md) :
    ∀ (l : List (_root_.Address × Ixon.Constant)) (acc : Keys md store roles)
      {q : ConstRef _root_.Address},
      ((∃ a c, (a, c) ∈ l ∧ resolve store a = some q) ∨ (acc.address[q]?).isSome = true) →
      (((l.foldl
        (fun (k : Keys md store roles) (p : _root_.Address × Ixon.Constant) =>
          let k := match h : resolve store p.1 with
            | some r => k.withAddress r p.1 h
            | none => k
          match h : keyOfAddress store roles p.1 with
          | some key => k.withKey p.1 key h
          | none => k)
        acc).address[q]?).isSome = true)
  | [], acc, _, hor => by
    rcases hor with ⟨_, _, hm, _⟩ | hsome
    · nomatch hm
    · exact hsome
  | (a₀, c₀) :: rest, acc, q, hor => by
    simp only [List.foldl_cons]
    let step1 : Keys md store roles :=
      match h : resolve store a₀ with
      | some r => acc.withAddress r a₀ h
      | none => acc
    let step2 : Keys md store roles :=
      match h : keyOfAddress store roles a₀ with
      | some key => step1.withKey a₀ key h
      | none => step1
    have hstep2_eq : step2.address = step1.address := by
      dsimp only [step2]
      split
      · unfold Keys.withKey; split <;> rfl
      · rfl
    have hpres : ∀ (hsome : (acc.address[q]?).isSome = true),
        (step2.address[q]?).isSome = true := by
      intro hsome
      rw [hstep2_eq]
      dsimp only [step1]
      split
      · unfold Keys.withAddress
        split
        · exact hsome
        · rw [Std.HashMap.getElem?_insert]
          split <;> simp [hsome]
      · exact hsome
    rcases hor with ⟨a, c, hm, hres⟩ | hsome
    · rcases List.mem_cons.mp hm with hhead | htail
      · cases hhead
        refine keysOf_address_isSome store roles rest step2 (Or.inr ?_)
        rw [hstep2_eq]
        dsimp only [step1]
        split
        · rename_i r hr
          rw [hres] at hr
          injection hr with hr_eq
          subst hr_eq
          unfold Keys.withAddress
          split
          · rename_i hc
            rwa [Std.HashMap.contains_eq_isSome_getElem?] at hc
          · simp
        · rename_i hr
          rw [hres] at hr
          cases hr
      · exact keysOf_address_isSome store roles rest step2 (Or.inl ⟨a, c, htail, hres⟩)
    · exact keysOf_address_isSome store roles rest step2 (Or.inr (hpres hsome))

/-- **`Ctx.memberKey` yields `AddressKey b a k`** for any record `(a, c) ∈ constants` resolving
uniquely to `q` in `streamContext`. -/
theorem streamContext_memberKey_addressKey {b : Binding} {t : Ix.Kernel.RoleTable}
    {pre : Prelude .anon} {constants : List (_root_.Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef _root_.Address → Option Ix.Kernel.ReducibilityHint}
    {a : _root_.Address} {c : Ixon.Constant} {q : ConstRef _root_.Address}
    {k : Ix.Kernel.Key .anon}
    (hadm : Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok t)
    (hmem : (a, c) ∈ constants)
    (hres : resolve
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).store
      a = some q)
    (hinj : ∀ a', resolve
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).store
      a' = some q → a' = a)
    (hmk :
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).memberKey
        q = .ok k) :
    IxVM.Refinement.AddressKey b a k := by
  let cx := Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint
  have hba := (Ix.Kernel.Admission.admitBinding_ok_iff _root_.Address.admissionHash b t).mp hadm
  have hofBytes : Ix.Kernel.RoleTable.ofBytes b.bytes = some t :=
    (Ix.Kernel.RoleTable.ofBytes_eq_some_iff b.bytes t).mpr hba.canonical
  cases hrole : cx.roles.names[q]? with
  | some k' =>
    have hk_eq : k' = k := by
      unfold Ctx.memberKey at hmk
      simpa [cx, hrole, pure, Except.pure] using hmk
    subst hk_eq
    have hroles_eq : cx.roles = bindingsOf cx.store t := rfl
    obtain ⟨ro, rfl⟩ := Ix.Cert.ReaderUnits.bindingsOf_keyed cx.store t q k'
      (by rwa [← hroles_eq])
    obtain ⟨a', hbound', hres'⟩ := Ix.Cert.ReaderKeys.bindings_role_origin cx.store t
      (by rwa [← hroles_eq])
    have ha_eq := hinj a' hres'
    subst ha_eq
    exact Or.inr ⟨t, ro, hofBytes,
      Ix.Cert.ReadingKeys.addressOf_of_bound hba.wellFormed hbound', rfl⟩
  | none =>
    have hall_mem :
        (a, c) ∈ (constants.toArray ++
          (pre.records ++ pre.evidence).filter (fun (x, _) =>
            !(constants.toArray.foldl (fun s (y, _) => s.insert y) ({} : Std.HashSet _root_.Address)).contains x)).toList := by
      rw [Array.toList_append]
      exact List.mem_append_left _ hmem
    have haddr_some : (cx.keys.address[q]?).isSome = true := by
      change ((keysOf cx.store cx.roles _).address[q]?).isSome = true
      unfold keysOf
      rw [← Array.foldl_toList]
      exact keysOf_address_isSome cx.store cx.roles _ {} (Or.inl ⟨a, c, hall_mem, hres⟩)
    obtain ⟨a', haddr⟩ := Option.isSome_iff_exists.mp haddr_some
    obtain ⟨hres', i, hid, rfl⟩ := Ctx.memberKey_of_unbound hrole haddr hmk
    have hi_eq : i = a := (Option.some.inj hid.symm).trans (hinj a' hres')
    subst hi_eq
    exact Or.inl rfl

/-- In `streamContext` over distinct stream keys, `(a, c) ∈ constants` implies `cx.store a = some c`. -/
theorem streamContext_store_of_mem {hash : ByteArray → _root_.Address} {t : Ix.Kernel.RoleTable}
    {pre : Prelude .anon} {constants : List (_root_.Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef _root_.Address → Option Ix.Kernel.ReducibilityHint}
    {a : _root_.Address} {c : Ixon.Constant}
    (hnd : (constants.map Prod.fst).Nodup)
    (hmem : (a, c) ∈ constants) :
    (Ix.Kernel.Admission.streamContext hash t pre constants blobs hint).store a = some c := by
  have hlookup : ∀ {xs : List (_root_.Address × Ixon.Constant)},
      (xs.map Prod.fst).Nodup → (a, c) ∈ xs → xs.lookup a = some c := by
    intro xs hnd_xs hm_xs
    induction xs with
    | nil => nomatch hm_xs
    | cons hd tl ih =>
      obtain ⟨k, v⟩ := hd
      rw [List.map_cons, List.nodup_cons] at hnd_xs
      simp only [List.lookup]
      rcases List.mem_cons.mp hm_xs with hhd | htl
      · cases hhd
        simp
      · have hne : a ≠ k := fun heq => hnd_xs.1 (List.mem_map.mpr ⟨(a, c), htl, heq⟩)
        simp [beq_eq_false_iff_ne.mpr hne, ih hnd_xs.2 htl]
  change ((recordMap constants.toArray)[a]? <|>
    ((recordMap (pre.records ++ pre.evidence))[a]? <|> none)) = some c
  rw [Ix.Cert.ReaderClosureKeys.recordMap_get]
  simp only [hlookup hnd hmem]
  rfl

/-- `AddressKey b a k` together with `¬ InertAt t a` rules out `inertKey k = true`. -/
theorem inertKey_false_of_addressKey_not_inert {b : Binding} {t : Ix.Kernel.RoleTable}
    {a : _root_.Address} {k : Ix.Kernel.Key .anon}
    (hadm : Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok t)
    (hak : IxVM.Refinement.AddressKey b a k)
    (hninert : ¬ IxVM.Consistency.InertAt t a) :
    IxVM.Consistency.inertKey k = false := by
  have hba := (Ix.Kernel.Admission.admitBinding_ok_iff _root_.Address.admissionHash b t).mp hadm
  have hofBytes : Ix.Kernel.RoleTable.ofBytes b.bytes = some t :=
    (Ix.Kernel.RoleTable.ofBytes_eq_some_iff b.bytes t).mpr hba.canonical
  rcases hak with rfl | ⟨t', r, hof', haddr, rfl⟩
  · rfl
  · rw [hofBytes] at hof'
    cases Option.some.inj hof'
    cases hin : r.inert with
    | false => exact hin
    | true => exact absurd ⟨r, hin, haddr⟩ hninert

end IxVM.Refinement.Assembly
