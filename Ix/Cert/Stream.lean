import Ix.Cert.Statement
import IxC.Kernel.Admission.Theorems

/-! # The reader succeeds over the compiled closure's stream (Route A, B3)

`IxonAccepts` (`Ix.Cert.Statement`) runs the certified entry over the
compiled closure's records in an order (`recordsOf ixe order`), the blobs
they reference (`blobsOf`) and the artifact's hints (`hintsOf`). The entry
first prepares the fold's input (`Ix.Kernel.Admission.prepareWith`): the
byte stage (batch limits, unique keys, authentication), the role table's
admission, canonical decoding, and the reader over the decoded records
(`readStream`, `readRecords` threading `Reader.State`). IxC proves what an
accepted preparation means; this file proves the converse that Route A needs:
the preparation **succeeds** on the compiled closure.

* `readRecords_complete`, `readStream_complete`: the reader's stream loop
  succeeds on every record-by-record reading (`StreamRead`, each record read
  against the state the records before it left), with distinct addresses:
  the converse of IxC's `readRecords_spec`. `readStream_complete` also requires
  the final state to keep the prelude's entries (`State.keepsPrelude`);
* the byte stage on the compiled closure: unique keys (`closure_unique`, from
  the order's distinctness and the blob map), authentication
  (`closure_authentic`, from `compileAuthentic`), and batch limits and
  canonical decoding under some limits (`closure_decodes`), given that every
  stored record decodes to a wire-valid constant whose canonical encoding is
  its stored bytes (`StoredCanonical`, the per-record codec over the
  compiled store);
* `prepareWith_ok`: the preparation succeeds from its stages' successes;
* **`closure_prepares`**: for a compiled artifact, an order of distinct
  addresses, `StoredCanonical`, an admitted role table and a stream reading
  of the decoded closure whose final state keeps the prelude's entries, the
  preparation succeeds within some limits, with
  the table's evidence resolved against the reading and the prelude's
  declarations in front; `closure_accepts`: with the fold's acceptance and
  the committed prelude, that is `IxonAccepts`.

The component theorems require `StoredCanonical` (the per-block codec over
the published store), a reading of every closure record, and `keeps` (the
final state keeps the prelude's entries). The compiler composition also
proves preservation at each earlier reader state; the final-state check
alone does not establish that property. -/

namespace Ix.Cert.Stream

open Ix.Kernel (ConstRef)
open Ix.Kernel.Admission (Limits Records Binding)
open Ix.Kernel.Reader

/-! ## The stream: the reader's loop succeeds on every record-by-record reading -/

theorem streamRead_cons_inv {md : Ix.Kernel.Mode} {cx : Ctx md} {st st' : State md} {a : Address}
    {c : Ixon.Constant} {rest : List (Address × Ixon.Constant)} {out : Array (CDecl md)}
    (h : StreamRead cx st ((a, c) :: rest) st' out) :
    ∃ r out', readRecord cx st a c = .ok r ∧ StreamRead cx (st.commit r) rest st' out' ∧
      out = r.decls ++ out' := by
  cases h with
  | cons read tail => exact ⟨_, _, read, tail, rfl⟩

/-- The loop of `readRecords`, over any body that reads one record per step:
on a record-by-record reading of fresh, distinct keys it succeeds. -/
theorem forIn_complete {md : Ix.Kernel.Mode} {cx : Ctx md}
    {f : (Address × Ixon.Constant) × Nat → Std.HashSet Address × State md × Array (CDecl md) →
      Except (ReadError × Nat) (ForInStep (Std.HashSet Address × State md × Array (CDecl md)))}
    (hf : ∀ x s r, s.1.contains x.1.1 = false → readRecord cx s.2.1 x.1.1 x.1.2 = .ok r →
      f x s = .ok (.yield (s.1.insert x.1.1, s.2.1.commit r, s.2.2 ++ r.decls))) :
    ∀ (l : List ((Address × Ixon.Constant) × Nat)) (s : Std.HashSet Address × State md × Array (CDecl md))
      (st' : State md) (out : Array (CDecl md)),
      StreamRead cx s.2.1 (l.map Prod.fst) st' out → (l.map (·.1.1)).Nodup →
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
    obtain ⟨r, out', read, tail, rfl⟩ := streamRead_cons_inv reads
    have hx : s.1.contains a = false := fresh _ (List.mem_cons_self ..)
    rw [List.forIn_cons, hf ((a, c), i) s r hx read]
    simp only [bind, Except.bind]
    have keys' := (List.nodup_cons.mp keys)
    obtain ⟨seen, ran⟩ := ih (s.1.insert a, s.2.1.commit r, s.2.2 ++ r.decls) st' out' tail keys'.2
      (fun y hy => by
        rw [Std.HashSet.contains_insert, Bool.or_eq_false_iff]
        refine ⟨?_, fresh y (List.mem_cons_of_mem _ hy)⟩
        rw [beq_eq_false_iff_ne]
        intro same
        exact keys'.1 (List.mem_map.2 ⟨y, hy, same.symm⟩))
    exact ⟨seen, by rw [ran]; simp [Array.append_assoc]⟩

/-- `readRecords`' loop and its result, over any body that reads one record
per step. -/
theorem readRecords_loop {md : Ix.Kernel.Mode} {cx : Ctx md}
    {f : (Address × Ixon.Constant) × Nat → Std.HashSet Address × State md × Array (CDecl md) →
      Except (ReadError × Nat) (ForInStep (Std.HashSet Address × State md × Array (CDecl md)))}
    (hf : ∀ x s r, s.1.contains x.1.1 = false → readRecord cx s.2.1 x.1.1 x.1.2 = .ok r →
      f x s = .ok (.yield (s.1.insert x.1.1, s.2.1.commit r, s.2.2 ++ r.decls)))
    {st st' : State md} {records : List (Address × Ixon.Constant)} {out : Array (CDecl md)}
    (reads : StreamRead cx st records st' out) (keys : (records.map Prod.fst).Nodup) :
    (forIn records.zipIdx (({} : Std.HashSet Address), st, (#[] : Array (CDecl md))) f >>=
      fun s => pure (s.2.1, s.2.2)) = (.ok (st', out) : Except (ReadError × Nat) _) := by
  have zipped : (records.zipIdx.map Prod.fst) = records := by simp
  obtain ⟨seen, ran⟩ := forIn_complete hf records.zipIdx ({}, st, #[]) st' out (by rw [zipped]; exact reads)
    (by
      have : records.zipIdx.map (·.1.1) = records.map Prod.fst := by
        rw [show (fun y : (Address × Ixon.Constant) × Nat => y.1.1) = Prod.fst ∘ Prod.fst from rfl,
          ← List.map_map, zipped]
      rw [this]; exact keys)
    (fun _ _ => by simp)
  rw [ran]
  simp [bind, Except.bind, pure, Except.pure]

/-- **The reader's stream succeeds** on every record-by-record reading of
records with distinct addresses: the converse of `readRecords_spec`. -/
theorem readRecords_complete {md : Ix.Kernel.Mode} {cx : Ctx md} {st st' : State md}
    {records : List (Address × Ixon.Constant)} {out : Array (CDecl md)}
    (reads : StreamRead cx st records st' out) (keys : (records.map Prod.fst).Nodup) :
    readRecords cx st records.toArray = .ok (st', out) := by
  unfold readRecords
  dsimp only
  rw [← Array.forIn_toList, Array.toList_zipIdx, List.toList_toArray]
  refine readRecords_loop ?_ reads keys
  intro x s r hx hr
  simp [hx, hr, pure, Except.pure]

/-- **The reading of decoded records succeeds** on every record-by-record
reading from the prelude's state whose final state keeps the prelude's entries
(`State.keepsPrelude`), with the table's evidence resolved against it. -/
theorem readStream_complete {hash : ByteArray → Address} {t : Ix.Kernel.RoleTable} {pre : Prelude .anon}
    {constants : List (Address × Ixon.Constant)} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {st' : State .anon} {decls : Array (CDecl .anon)}
    (reads : StreamRead (Ix.Kernel.Admission.streamContext hash t pre constants blobs hint) pre.state
      constants st' decls)
    (keys : (constants.map Prod.fst).Nodup) (keeps : State.keepsPrelude pre.state st' = true) :
    Ix.Kernel.Admission.readStream hash t pre constants blobs hint =
      .ok (evidenceOf (Ix.Kernel.Admission.streamContext hash t pre constants blobs hint) st' t, decls) := by
  unfold Ix.Kernel.Admission.readStream
  dsimp only
  rw [readRecords_complete reads keys]
  simp [keeps, pure, Except.pure]

/-! ## The byte stage on the compiled closure -/

/-- Every stored record of `order` decodes (`recordAt`) to a wire-valid
constant whose canonical encoding is its stored bytes: the per-record codec
over the compiled store. -/
def StoredCanonical (ixe : Ixon.Env) (order : List Address) : Prop :=
  ∀ a ∈ order, ∀ lc, ixe.consts.get? a = some lc →
    ∃ c, lc.get? = some c ∧ c.wireWF ∧ Ixon.serConstant c = lc.rawBytes

/-- The decoded records at `order`. -/
def decodedOf (ixe : Ixon.Env) (order : List Address) : List (Address × Ixon.Constant) :=
  order.filterMap fun a => (recordAt ixe a).map (a, ·)

theorem recordsOf_cons (ixe : Ixon.Env) (a : Address) (order : List Address) :
    recordsOf ixe (a :: order) =
      ((ixe.consts.get? a).map fun lc => (a, lc.rawBytes)).toList ++ recordsOf ixe order := by
  unfold recordsOf
  rw [List.filterMap_cons]
  cases ixe.consts.get? a <;> rfl

theorem decodedOf_cons (ixe : Ixon.Env) (a : Address) (order : List Address) :
    decodedOf ixe (a :: order) = ((recordAt ixe a).map (a, ·)).toList ++ decodedOf ixe order := by
  unfold decodedOf
  rw [List.filterMap_cons]
  cases recordAt ixe a <;> rfl

theorem recordsOf_keys (ixe : Ixon.Env) :
    ∀ order : List Address, ((recordsOf ixe order).map Prod.fst).Sublist order
  | [] => by simp [recordsOf]
  | a :: order => by
    rw [recordsOf_cons]
    cases ixe.consts.get? a with
    | none => exact (recordsOf_keys ixe order).cons a
    | some lc => exact (recordsOf_keys ixe order).cons_cons a

theorem decodedOf_keys (ixe : Ixon.Env) :
    ∀ order : List Address, ((decodedOf ixe order).map Prod.fst).Sublist order
  | [] => by simp [decodedOf]
  | a :: order => by
    rw [decodedOf_cons]
    cases recordAt ixe a with
    | none => exact (decodedOf_keys ixe order).cons a
    | some c => exact (decodedOf_keys ixe order).cons_cons a

theorem mem_blobsOf {ixe : Ixon.Env} {order : List Address} {entry : Address × ByteArray}
    (h : entry ∈ blobsOf ixe order) : ixe.blobs.get? entry.1 = some entry.2 := by
  unfold blobsOf at h
  exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp (List.mem_filter.mp h).1

theorem blobsOf_keys (ixe : Ixon.Env) (order : List Address) :
    ((blobsOf ixe order).map Prod.fst).Nodup := by
  unfold blobsOf
  have keys : (ixe.blobs.toList.map Prod.fst).Nodup := by
    rw [Std.HashMap.map_fst_toList_eq_keys]; exact Std.HashMap.nodup_keys
  exact keys.sublist (List.Sublist.map _ List.filter_sublist)

/-- **Unique keys on the compiled closure**: the records of an order of
distinct addresses, and the blobs they reference (keys of the blob map). -/
theorem closure_unique (ixe : Ixon.Env) {order : List Address} (nodup : order.Nodup) :
    Ix.Kernel.Admission.UniqueKeys (recordsOf ixe order) (blobsOf ixe order) :=
  ⟨nodup.sublist (recordsOf_keys ixe order), blobsOf_keys ixe order⟩

theorem mem_recordsOf {ixe : Ixon.Env} {order : List Address} {entry : Address × ByteArray}
    (h : entry ∈ recordsOf ixe order) :
    entry.1 ∈ order ∧ ∃ lc, ixe.consts.get? entry.1 = some lc ∧ entry.2 = lc.rawBytes := by
  unfold recordsOf at h
  obtain ⟨a, ha, he⟩ := List.mem_filterMap.mp h
  cases hl : ixe.consts.get? a with
  | none => rw [hl] at he; cases he
  | some lc =>
    simp only [hl, Option.map_some, Option.some.injEq] at he
    subst he
    exact ⟨ha, lc, hl, rfl⟩

/-- **Authentication on the compiled closure** (`compileAuthentic`): every
record and blob is stored under the admission hash of its bytes. -/
theorem closure_authentic {env : Ix.Environment} {ixe : Ixon.Env} (compiled : compile env = .ok ixe)
    (order : List Address) :
    Ix.Kernel.Admission.Authentic Address.admissionHash (recordsOf ixe order) (blobsOf ixe order) := by
  obtain ⟨records, blobs⟩ := compileAuthentic env ixe compiled
  refine ⟨fun entry h => ?_, fun entry h => ?_⟩
  · obtain ⟨-, lc, hl, he⟩ := mem_recordsOf h
    rw [he]; exact records _ _ hl
  · exact blobs _ _ (mem_blobsOf h)

/-- The universe nodes of decoded records, summed. -/
def nodesOf : List (Address × Ixon.Constant) → Nat
  | [] => 0
  | (_, c) :: rest => Ixon.Bounded.univNodes c.univs + nodesOf rest

theorem size_le_payload {records : Records} {entry : Address × ByteArray} (h : entry ∈ records) :
    entry.2.size ≤ Ix.Kernel.Admission.payloadBytes records := by
  induction records with
  | nil => cases h
  | cons head rest ih =>
    obtain ⟨a, bytes⟩ := head
    simp only [Ix.Kernel.Admission.payloadBytes]
    rcases List.mem_cons.mp h with rfl | h
    · show bytes.size ≤ _; omega
    · have := ih h; omega

theorem nodes_le {constants : List (Address × Ixon.Constant)} {entry : Address × Ixon.Constant}
    (h : entry ∈ constants) : Ixon.Bounded.univNodes entry.2.univs ≤ nodesOf constants := by
  induction constants with
  | nil => cases h
  | cons head rest ih =>
    obtain ⟨a, c⟩ := head
    simp only [nodesOf]
    rcases List.mem_cons.mp h with rfl | h
    · show Ixon.Bounded.univNodes c.univs ≤ _; omega
    · have := ih h; omega

/-- The decoded closure reads canonically under any per-record limits that
fit every record's bytes and universe nodes. -/
theorem closure_reads (ixe : Ixon.Env) (limits : Limits) :
    ∀ order : List Address, StoredCanonical ixe order →
      (∀ entry ∈ recordsOf ixe order, entry.2.size ≤ limits.maxRecordBytes) →
      (∀ entry ∈ decodedOf ixe order, Ixon.Bounded.univNodes entry.2.univs ≤ limits.maxRecordUnivNodes) →
      Ix.Kernel.Admission.RecordsRead limits (recordsOf ixe order) (decodedOf ixe order)
  | [], _, _, _ => by simpa [recordsOf, decodedOf] using Ix.Kernel.Admission.RecordsRead.nil
  | a :: order, canonical, bytesFit, nodesFit => by
    have tail := closure_reads ixe limits order (fun b hb => canonical b (List.mem_cons_of_mem _ hb))
      (fun e he => bytesFit e (by rw [recordsOf_cons]; exact List.mem_append_right _ he))
      (fun e he => nodesFit e (by rw [decodedOf_cons]; exact List.mem_append_right _ he))
    rw [recordsOf_cons, decodedOf_cons]
    cases hl : ixe.consts.get? a with
    | none =>
      have : recordAt ixe a = none := by unfold recordAt; rw [hl]; rfl
      simpa [this] using tail
    | some lc =>
      obtain ⟨c, hc, wire, encoded⟩ := canonical a (List.mem_cons_self ..) lc hl
      have hr : recordAt ixe a = some c := by unfold recordAt; rw [hl]; exact hc
      simp only [Option.map_some, Option.toList_some, hr, List.singleton_append]
      refine .cons ⟨wire, encoded, ?_, ?_⟩ tail
      · exact bytesFit (a, lc.rawBytes) (by rw [recordsOf_cons, hl]; simp)
      · exact nodesFit (a, c) (by rw [decodedOf_cons, hr]; simp)

/-- **Batch limits and canonical decoding on the compiled closure**, under
some limits: those that fit exactly the closure's records and blobs. -/
theorem closure_decodes (ixe : Ixon.Env) {order : List Address} (canonical : StoredCanonical ixe order) :
    ∃ limits : Limits, Ix.Kernel.Admission.WithinBatch limits (recordsOf ixe order) (blobsOf ixe order) ∧
      Ix.Kernel.Admission.RecordsRead limits (recordsOf ixe order) (decodedOf ixe order) := by
  let records := recordsOf ixe order
  let blobs := blobsOf ixe order
  let limits : Limits :=
    { maxRecords := records.length
      maxBlobs := blobs.length
      maxTotalBytes := Ix.Kernel.Admission.payloadBytes records + Ix.Kernel.Admission.payloadBytes blobs
      maxRecordBytes := Ix.Kernel.Admission.payloadBytes records
      maxRecordUnivNodes := nodesOf (decodedOf ixe order) }
  refine ⟨limits, ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩, ?_⟩
  exact closure_reads ixe limits order canonical (fun _ h => size_le_payload h) (fun _ h => nodes_le h)

/-! ## The preparation succeeds -/

/-- **The preparation succeeds from its stages' successes**: batch limits,
unique keys, authentication, the role table's admission, canonical decoding
and a record-by-record reading of the decoded records that keeps the prelude's
entries (`State.keepsPrelude`). -/
theorem prepareWith_ok {hash : ByteArray → Address} {binding : Binding} {pre : Prelude .anon}
    {limits : Limits} {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {t : Ix.Kernel.RoleTable}
    {constants : List (Address × Ixon.Constant)} {st' : State .anon} {decls : Array (CDecl .anon)}
    (batch : Ix.Kernel.Admission.WithinBatch limits records blobs)
    (unique : Ix.Kernel.Admission.UniqueKeys records blobs)
    (authentic : Ix.Kernel.Admission.Authentic hash records blobs)
    (admitted : Ix.Kernel.Admission.admitBinding hash binding = .ok t)
    (decoded : Ix.Kernel.Admission.RecordsRead limits records constants)
    (reads : StreamRead (Ix.Kernel.Admission.streamContext hash t pre constants blobs hint) pre.state
      constants st' decls) (keeps : State.keepsPrelude pre.state st' = true) :
    Ix.Kernel.Admission.prepareWith hash binding pre limits records blobs hint =
      .ok (evidenceOf (Ix.Kernel.Admission.streamContext hash t pre constants blobs hint) st' t,
        Ix.Kernel.Frontend.preparePrelude pre.ix decls) := by
  have hp := (Ix.Kernel.Admission.preflight_ok_iff limits records blobs).mpr batch
  have hu := (Ix.Kernel.Admission.uniqueKeys_ok_iff records blobs).mpr unique
  have ha := (Ix.Kernel.Admission.authenticate_ok_iff hash records blobs).mpr authentic
  have hd := (Ix.Kernel.Admission.decodeRecords_ok_iff limits records constants).mpr decoded
  have keys : (constants.map Prod.fst).Nodup := decoded.keys ▸ unique.1
  have hs := readStream_complete reads keys keeps
  unfold Ix.Kernel.Admission.prepareWith
  simp only [hp, hu, ha, admitted, hd, hs, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- **The reader succeeds over the compiled closure's stream** (Route A,
B3): for the artifact `compile` returns, an order of distinct addresses
whose stored records decode canonically, an admitted role table and a
record-by-record reading of the decoded closure from the prelude's state that keeps
the prelude's entries (`State.keepsPrelude`),
the entry's preparation succeeds within some limits, with the table's
evidence resolved against the reading and the prelude's declarations in
front. -/
theorem closure_prepares {env : Ix.Environment} {ixe : Ixon.Env} (compiled : compile env = .ok ixe)
    {order : List Address} (nodup : order.Nodup) (canonical : StoredCanonical ixe order)
    {binding : Binding} {t : Ix.Kernel.RoleTable}
    (admitted : Ix.Kernel.Admission.admitBinding Address.admissionHash binding = .ok t)
    (pre : Prelude .anon) {st' : State .anon} {decls : Array (CDecl .anon)}
    (reads : StreamRead (Ix.Kernel.Admission.streamContext Address.admissionHash t pre (decodedOf ixe order)
      (blobsOf ixe order) (hintsOf ixe)) pre.state (decodedOf ixe order) st' decls)
    (keeps : State.keepsPrelude pre.state st' = true) :
    ∃ limits, Ix.Kernel.Admission.prepareWith Address.admissionHash binding pre limits (recordsOf ixe order)
        (blobsOf ixe order) (hintsOf ixe) =
      .ok (evidenceOf (Ix.Kernel.Admission.streamContext Address.admissionHash t pre (decodedOf ixe order)
          (blobsOf ixe order) (hintsOf ixe)) st' t,
        Ix.Kernel.Frontend.preparePrelude pre.ix decls) := by
  obtain ⟨limits, batch, decoded⟩ := closure_decodes ixe canonical
  exact ⟨limits, prepareWith_ok batch (closure_unique ixe nodup) (closure_authentic compiled order) admitted
    decoded reads keeps⟩

/-- The entry over a source of preludes succeeds from the prelude, the
preparation and the fold. -/
theorem checkBytesUsing_ok {prelude : Ix.Kernel.RoleTable → Except String (Prelude .anon)}
    {hash : ByteArray → Address} {binding : Binding} {limits : Limits} {records : Records}
    {blobs : Ix.Kernel.Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {t : Ix.Kernel.RoleTable} {pre : Prelude .anon} {ev : Ix.Kernel.Evidences .anon}
    {ds : Array (Ix.Kernel.Declaration .anon)} {envA : Ix.Kernel.Env .anon}
    (admitted : Ix.Kernel.Admission.admitBinding hash binding = .ok t) (hq : prelude t = .ok pre)
    (prepared : Ix.Kernel.Admission.prepareWith hash binding pre limits records blobs hint = .ok (ev, ds))
    (checked : Ix.Kernel.Cached.checkDecls .verified ev ds = .ok envA) :
    Ix.Kernel.Admission.checkBytesUsing prelude hash binding limits records blobs hint = .ok envA := by
  unfold Ix.Kernel.Admission.checkBytesUsing Ix.Kernel.Admission.checkBytesWith
  simp only [admitted, hq, prepared, checked, Except.mapError, bind, Except.bind]

/-- **With the fold's acceptance, that is `IxonAccepts`**: under the
committed prelude for the admitted table, if the verified fold accepts the
prepared declarations at the table's evidence, the certified entry accepts
the compiled closure. -/
theorem closure_accepts {env : Ix.Environment} {ixe : Ixon.Env} (compiled : compile env = .ok ixe)
    {S : Address → Prop} {order : List Address} (closure : ClosureOrder ixe S order)
    (canonical : StoredCanonical ixe order) {binding : Binding} {t : Ix.Kernel.RoleTable}
    (admitted : Ix.Kernel.Admission.admitBinding Address.admissionHash binding = .ok t)
    {pre : Prelude .anon} (prelude : preludeFor t = .ok pre)
    {st' : State .anon} {decls : Array (CDecl .anon)}
    (reads : StreamRead (Ix.Kernel.Admission.streamContext Address.admissionHash t pre (decodedOf ixe order)
      (blobsOf ixe order) (hintsOf ixe)) pre.state (decodedOf ixe order) st' decls)
    (keeps : State.keepsPrelude pre.state st' = true)
    {envA : Ix.Kernel.Env .anon}
    (checked : Ix.Kernel.Cached.checkDecls .verified
      (evidenceOf (Ix.Kernel.Admission.streamContext Address.admissionHash t pre (decodedOf ixe order)
        (blobsOf ixe order) (hintsOf ixe)) st' t)
      (Ix.Kernel.Frontend.preparePrelude pre.ix decls) = .ok envA) :
    ∃ limits, IxonAccepts binding limits ixe S order envA := by
  obtain ⟨limits, prepared⟩ := closure_prepares compiled closure.nodup canonical admitted pre reads keeps
  exact ⟨limits, closure, checkBytesUsing_ok admitted prelude prepared checked⟩

end Ix.Cert.Stream
