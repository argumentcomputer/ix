import Ix.Cert.ReferenceFronts
import Ix.Cert.Stream
import Ix.Cert.SourcePublication

/-! Actual admitted records supply their prepared definition indices. Reader
prefixes and checker prefixes remain distinct; no closure or source baseline
is inferred from acceptance of the supplied batch. -/
namespace Ix.Cert.AdmittedTargetFronts
open Ix.Kernel Ix.Kernel.Reader Ix.Kernel.Admission Ix.Cert.ReferenceFronts
universe w

/-- One execution's preparation, reused for every selected occurrence. -/
structure Prepared (binding : Binding) (limits : Limits) (records : Records)
    (blobs : Ingress.Blobs) (hint : ConstRef Address → Option ReducibilityHint) (envA : Env .anon) where
  table : RoleTable
  pre : Prelude .anon
  constants : Ingress.Constants
  ev : Evidences .anon
  decls : Array (Declaration .anon)
  admitted : admitBinding Address.admissionHash binding = .ok table
  prelude : preludeFor table = .ok pre
  decoded : decodeRecords limits records = .ok constants
  read : readStream Address.admissionHash table pre constants blobs hint = .ok (ev, decls)
  prepared : prepareWith Address.admissionHash binding pre limits records blobs hint =
    .ok (ev, Frontend.preparePrelude pre.ix decls)
  checked : Cached.checkDecls .verified ev (Frontend.preparePrelude pre.ix decls) = .ok envA

theorem prepared_of_check {binding limits records blobs hint envA}
    (run : Ixon.Authenticated.checkBytes binding limits records blobs hint = .ok envA) :
    Nonempty (Prepared binding limits records blobs hint envA) := by
  obtain ⟨table, pre, admitted, prelude, run⟩ := checkBytes_with run
  obtain ⟨ev, ds, prepared, checked⟩ := checkBytesWith_checkDecls run
  cases batch : preflight limits records blobs with
  | error e => simp [prepareWith, batch, Except.mapError, bind, Except.bind] at prepared
  | ok u =>
    cases unique : uniqueKeys records blobs with
    | error e => simp [prepareWith, batch, unique, Except.mapError, bind, Except.bind] at prepared
    | ok v =>
      cases auth : authenticate Address.admissionHash records blobs with
      | error e => simp [prepareWith, batch, unique, auth, Except.mapError, bind, Except.bind] at prepared
      | ok z =>
        cases decoded : decodeRecords limits records with
        | error e => simp [prepareWith, batch, unique, auth, admitted, decoded, Except.mapError, bind, Except.bind] at prepared
        | ok constants =>
          cases read : readStream Address.admissionHash table pre constants blobs hint with
          | error e => simp [prepareWith, batch, unique, auth, admitted, decoded, read, Except.mapError, bind, Except.bind] at prepared
          | ok pair =>
            obtain ⟨ev', decls⟩ := pair
            have shape := prepared
            simp only [prepareWith, batch, unique, auth, admitted, decoded, read, Except.mapError,
              bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at shape
            obtain ⟨rfl, rfl⟩ := shape
            exact ⟨⟨table, pre, constants, ev', decls, admitted, prelude, decoded, read, prepared, checked⟩⟩

theorem decoded_at {limits records constants} (read : RecordsRead limits records constants)
    {j : Nat} {a : Address} {bytes : ByteArray} (atByte : records[j]? = some (a, bytes)) :
    ∃ c, constants[j]? = some (a, c) ∧
      Ixon.Verify.Canonical.Reads limits.maxRecordBytes limits.maxRecordUnivNodes bytes c := by
  induction read generalizing j with
  | nil => simp at atByte
  | cons reads tail ih =>
    cases j with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at atByte
              obtain ⟨rfl, rfl⟩ := atByte
              exact ⟨_, rfl, reads⟩
    | succ j => exact ih atByte

/-- The exact record position in one StreamRead, before preparation moves declarations. -/
def RecordAt {md : Mode} (cx : Ctx md) (start fin : State md)
    (constants : Ingress.Constants) (decls : Array (Declaration md)) (j : Nat)
    (a : Address) (c : Ixon.Constant) (st : State md) (r : Read md) : Prop :=
  constants[j]? = some (a, c) ∧ ∃ before after,
    StreamRead cx start (constants.take j) st before ∧ readRecord cx st a c = .ok r ∧
    StreamRead cx (st.commit r) (constants.drop (j + 1)) fin after ∧
    decls = before ++ r.decls ++ after

theorem stream_at {md : Mode} {cx : Ctx md} {start fin : State md}
    {constants : Ingress.Constants} {decls : Array (Declaration md)}
    (stream : StreamRead cx start constants fin decls)
    {j : Nat} {a : Address} {c : Ixon.Constant} (atRecord : constants[j]? = some (a, c)) :
    ∃ st r, RecordAt cx start fin constants decls j a c st r := by
  induction stream generalizing j with
  | nil => simp at atRecord
  | @cons st fin a' c' r rest out read tail ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at atRecord
      obtain ⟨rfl, rfl⟩ := atRecord
      exact ⟨st, r, rfl, #[], out, .nil, read, tail, by simp⟩
    | succ j =>
      obtain ⟨mid, current, atTail, before, after, pref, step, suff, shape⟩ := ih atRecord
      refine ⟨mid, current, atRecord, r.decls ++ before, after, ?_, step, ?_, ?_⟩
      · exact .cons read pref
      · simpa only [List.drop_succ_cons] using suff
      · simp only [shape, Array.append_assoc]

variable {binding : Binding} {limits : Limits} {records : Records} {blobs : Ingress.Blobs}
  {hint : ConstRef Address → Option ReducibilityHint} {envA : Env .anon}

/-- Target wire origin plus the SAME prepared checker front. -/
def DefinitionAt (p : Prepared binding limits records blobs hint envA) (j : Nat)
    (a : Address) (c : Ixon.Constant) (d : Ixon.Definition) : Prop :=
  let cx := streamContext Address.admissionHash p.table p.pre p.constants blobs hint
  ∃ fin st r key ty value actualHint i F before expected checked,
    StreamRead cx p.pre.state p.constants fin p.decls ∧
    p.ev = evidenceOf cx fin p.table ∧ State.keepsPrelude p.pre.state fin = true ∧
    RecordAt cx p.pre.state fin p.constants p.decls j a c st r ∧
    cx.memberKey (.member a 0) = .ok key ∧
    (definitionReader cx a c d).read d.typ = .ok ty ∧
    (definitionReader cx a c d).read d.value = .ok value ∧
    let cv := (⟨key, singletonLps d.lvls, ty⟩ : Ix.Kernel.ConstantVal .anon)
    let raw := (projRewrite st cv value).getD value
    r.decls = #[.defnDecl cv raw actualHint] ∧
    DefinitionFrontAt p.ev (Frontend.preparePrelude p.pre.ix p.decls).toList envA
      i cv raw actualHint F before expected checked

theorem Prepared.singleton (V : Type w) [SetTheory V]
    (p : Prepared binding limits records blobs hint envA) {j a c d}
    (atRecord : p.constants[j]? = some (a, c)) (info : c.info = .defn d) (kind : d.kind = .defn) :
    DefinitionAt p j a c d := by
  obtain ⟨fin, stream, evidence, keeps⟩ := readStream_spec p.read
  obtain ⟨st, r, trace⟩ := stream_at stream atRecord
  obtain ⟨_, pref, suff, beforeRun, recordRun, afterRun, shape⟩ := trace
  obtain ⟨decl, reading, decls⟩ := readRecord_singleton (by simp [isSingleton, info]) recordRun
  cases reading with
  | @defn d' key ty value decl found keyed type body form =>
    rw [info] at found
    cases found
    rw [kind] at form
    cases form with
    | defn actualHint =>
      let cv : Ix.Kernel.ConstantVal .anon := ⟨key, singletonLps d.lvls, ty⟩
      let raw := (projRewrite st cv value).getD value
      have member : .defnDecl cv raw actualHint ∈ p.decls := by simp [shape, decls, cv, raw]
      have kept := Frontend.mem_preparePrelude (pre := p.pre.ix) member
      obtain ⟨i, atDecl⟩ := List.mem_iff_getElem?.mp (Array.mem_toList_iff.mpr kept)
      obtain ⟨F, before, expected, checked, front⟩ := reference_definition_front_at
        (Cached.checkDecls_refines_ref V rfl p.checked) atDecl
      exact ⟨fin, st, r, key, ty, value, actualHint, i, F, before, expected, checked,
        stream, evidence, keeps, ⟨atRecord, pref, suff, beforeRun, recordRun, afterRun, shape⟩,
        keyed, type, body, decls, front⟩
  | axio found => rw [info] at found; cases found
  | quot found => rw [info] at found; cases found

/-- The selected-root consumer keeps exact artifact bytes/hints and one
preparation. Batch occurrence is explicit; no closure coverage is inferred. -/
theorem selected_fronts (V : Type w) [SetTheory V] {binding limits ixe order envA}
    (nodes : Ix.Map Ix.Name Ix.Compile.SourceGraph.Node) (cs : Ix.Compile.ChangedSet.ChangedSet)
    (run : Ixon.Authenticated.checkBytes binding limits (recordsOf ixe order) (blobsOf ixe order)
      (hintsOf ixe) = .ok envA) :
    ∃ p : Prepared binding limits (recordsOf ixe order) (blobsOf ixe order) (hintsOf ixe) envA,
      ∀ r ∈ SourcePublication.selectOriginal nodes cs ixe, ∀ j bytes,
        (recordsOf ixe order)[j]? = some (r.address, bytes) →
        ∃ c, p.constants[j]? = some (r.address, c) ∧
          Ixon.Verify.Canonical.Reads limits.maxRecordBytes limits.maxRecordUnivNodes bytes c ∧
          ∀ d, c.info = .defn d → d.kind = .defn → DefinitionAt p j r.address c d := by
  obtain ⟨p⟩ := prepared_of_check run
  refine ⟨p, fun r _ j bytes atByte => ?_⟩
  obtain ⟨c, atRecord, read⟩ := decoded_at (decodeRecords_ok_iff .. |>.mp p.decoded) atByte
  exact ⟨c, atRecord, read, fun d info kind => p.singleton V atRecord info kind⟩

end Ix.Cert.AdmittedTargetFronts
