import Ix.Cert.DefinitionSnapshots

/-! Actual theorem fronts keep the checked proof separate from raw theorem
storage. Prefixes and counters come from the creating step's actual suffix;
no theorem value semantics or candidate checking is supplied here. -/
namespace Ix.Cert.TheoremSnapshots
open Ix.Kernel Ix.Kernel.Semantics
universe w
variable {md : Mode}

/-- The same actual reference run supplies the theorem's propositionhood and
annotated proof. Only the raw post-reader body is stored under thmInfo. -/
def TheoremFrontAt (ev : Evidences md) (ds : List (Declaration md)) (envA : Env md)
    (i : Nat) (cv : Ix.Kernel.ConstantVal md) (raw : Ix.Kernel.Expr md)
    (F : Nat) (before : Env md) (expected checkedProof : Ix.Kernel.Expr md) : Prop :=
  let step := checkDecl .verified (fueledOps .verified F) ev
  let after : Env md := ⟨.thmInfo ⟨cv.name, cv.levelParams, expected⟩ raw :: before.consts⟩
  ds[i]? = some (.thmDecl cv raw) ∧
  checkDeclsPure .verified (fueledOps .verified F) ev ds = .ok envA ∧
  (ds.take i).foldlM step Env.empty = .ok before ∧
  step before (.thmDecl cv raw) = .ok after ∧
  (ds.drop (i + 1)).foldlM step after = .ok envA ∧
  ConstantValRun .verified F before cv expected ∧
  (∃ stype u, inferTypeCore .verified before F 0 expected = .ok stype ∧
    ensureSortCore .verified before F 0 stype = .ok u ∧ Level.isEquiv u .zero = some true) ∧
  ValueFrontRun .verified F before cv raw expected checkedProof ∧
  envA.find? cv.name = some (.thmInfo ⟨cv.name, cv.levelParams, expected⟩ raw)

theorem reference_theorem_front_at
    {ev : Evidences md} {ds : List (Declaration md)} {envA : Env md}
    {i : Nat} {cv : Ix.Kernel.ConstantVal md} {raw : Ix.Kernel.Expr md}
    (accepted : Cached.AcceptsRef .verified ev ds envA)
    (atDecl : ds[i]? = some (.thmDecl cv raw)) :
    ∃ F before expected checkedProof,
      TheoremFrontAt ev ds envA i cv raw F before expected checkedProof := by
  obtain ⟨F, whole⟩ := accepted
  obtain ⟨bound, atValue⟩ := List.getElem?_eq_some_iff.mp atDecl
  have split : ds = ds.take i ++ .thmDecl cv raw :: ds.drop (i + 1) := by
    have eq := List.take_append_drop i ds
    rw [List.drop_eq_getElem_cons bound, atValue] at eq
    exact eq.symm
  have run := whole
  unfold checkDeclsPure at run
  rw [split] at run
  obtain ⟨before, prefixRun, rest⟩ := foldlM_append_ok run
  rw [List.foldlM_cons] at rest
  cases stepRun : checkDecl .verified (fueledOps .verified F) ev before (.thmDecl cv raw) with
  | error err => rw [stepRun] at rest; exact nomatch rest
  | ok after =>
    rw [stepRun] at rest
    change (ds.drop (i + 1)).foldlM (checkDecl .verified (fueledOps .verified F) ev) after = .ok envA at rest
    obtain ⟨expected, checkedProof, header, prop, value, installed⟩ := declThmRun_of stepRun
    have immediate : after.find? cv.name = some (.thmInfo ⟨cv.name, cv.levelParams, expected⟩ raw) := by
      rw [installed]
      simp only [Env.find?_cons, Ix.Kernel.ConstantInfo.name, Ix.Kernel.ConstantInfo.toConstantVal, ↓reduceIte]
    have growth := foldlM_checkDecl_post .verified (fueledOps .verified F) ev
      (ds.drop (i + 1)) after envA rest
    refine ⟨F, before, expected, checkedProof, atDecl, whole, prefixRun, ?_, ?_, header, prop, value,
      growth.persist immediate⟩
    · exact installed ▸ stepRun
    · exact installed ▸ rest

private theorem idxSpec_skip (key : Key md) (new old : List (Ix.Kernel.ConstantInfo md))
    (fresh : ∀ c ∈ new, c.name ≠ key) : idxSpec (new ++ old) key = idxSpec old key := by
  induction new with
  | nil => rfl
  | cons c new ih =>
    have no := beq_eq_false_iff_ne.mpr (fresh c List.mem_cons_self)
    simp only [List.cons_append, idxSpec, no, Bool.false_eq_true, ite_false]
    exact ih fun d member => fresh d (List.mem_cons_of_mem _ member)

/-- The raw theorem's actual installation position, without an offset or
uniqueness premise. The annotation witness does not enter the stored value. -/
theorem counter_prefix {ev : Evidences md} {ds : List (Declaration md)} {envA before : Env md}
    {i F : Nat} {cv : Ix.Kernel.ConstantVal md} {raw expected checkedProof : Ix.Kernel.Expr md}
    (front : TheoremFrontAt ev ds envA i cv raw F before expected checkedProof) :
    (mkFEnv envA).idx[cv.name]? = some (before.consts.length,
      .thmInfo ⟨cv.name, cv.levelParams, expected⟩ raw) ∧ envA.prefixTo before.consts.length = before := by
  let stored : Ix.Kernel.ConstantInfo md := .thmInfo ⟨cv.name, cv.levelParams, expected⟩ raw
  let after : Env md := ⟨stored :: before.consts⟩
  obtain ⟨_, _, _, _, suffixRun, _, _, _, _⟩ := front
  have growth := foldlM_checkDecl_post .verified (fueledOps .verified F) ev
    (ds.drop (i + 1)) after envA suffixRun
  obtain ⟨new, extent, fresh⟩ := growth
  have atHead : after.find? cv.name = some stored := by
    simp [after, stored, Env.find?, Ix.Kernel.ConstantInfo.name, Ix.Kernel.ConstantInfo.toConstantVal]
  have other : ∀ c ∈ new, c.name ≠ cv.name := by
    intro c member same
    have absent := (fresh c member).2
    rw [same, atHead] at absent
    cases absent
  constructor
  · rw [mkFEnv_idx, extent, idxSpec_skip cv.name new after.consts other]
    simp [after, stored, idxSpec, Ix.Kernel.ConstantInfo.name, Ix.Kernel.ConstantInfo.toConstantVal]
  · exact Env.prefixTo_of_extends (env := before) (env' := envA) (new := new ++ [stored])
      (by simpa [after, List.append_assoc] using extent)

private theorem checked_names {ev : Evidences md} {ds : Array (Declaration md)} {envA : Env md}
    (run : Cached.checkDecls .verified ev ds = .ok envA) : NodupNames envA := by
  obtain ⟨fc, finalEnv⟩ := Cached.checkDecls_fullyChecked .verified run
  obtain ⟨n, s, trace⟩ := fc.1.run
  have chain := (Cached.installRun_trace .verified trace (Cached.PushChain.refl Env.empty)).1
  rw [← finalEnv]
  exact chain.2.2 List.nodup_nil

/-- The actual accepted theorem supplies its logical prefix and bounded
lookup view. The physical env remains final; the current key stays hidden. -/
theorem checked_context (V : Type w) [SetTheory V]
    {ev : Evidences md} {ds : Array (Declaration md)} {envA : Env md}
    {i : Nat} {cv : Ix.Kernel.ConstantVal md} {raw : Ix.Kernel.Expr md}
    (run : Cached.checkDecls .verified ev ds = .ok envA)
    (atDecl : ds.toList[i]? = some (.thmDecl cv raw)) :
    ∃ F before expected checkedProof,
      TheoremFrontAt ev ds.toList envA i cv raw F before expected checkedProof ∧
      (mkFEnv envA).idx[cv.name]? = some (before.consts.length,
        .thmInfo ⟨cv.name, cv.levelParams, expected⟩ raw) ∧
      envA.prefixTo before.consts.length = before ∧
      ((mkFEnv envA).restrictTo before.consts.length).env = envA ∧
      (∀ n, ((mkFEnv envA).restrictTo before.consts.length).find? n = before.find? n) ∧
      ((mkFEnv envA).restrictTo before.consts.length).find? cv.name = none := by
  obtain ⟨F, before, expected, checkedProof, front⟩ := reference_theorem_front_at
    (Cached.checkDecls_refines_ref V rfl run) atDecl
  obtain ⟨counter, logical⟩ := counter_prefix front
  refine ⟨F, before, expected, checkedProof, front, counter, logical, rfl, ?_, ?_⟩
  · intro n
    rw [mkFEnv_find?_visibleBelow envA _ n (checked_names run), logical]
  · simp [FEnv.find?, FEnv.restrictTo, counter]

open Ix.Kernel.Reader Ix.Kernel.Admission Ix.Cert.AdmittedTargetFronts
open Ix.Cert.DefinitionSnapshots (Receipt checkReceipt checkReceipt_ok)

structure Snapshot where
  position : Nat
  cv : Ix.Kernel.ConstantVal .anon
  raw : Ix.Kernel.Expr .anon
  counter : Nat
  expected : Ix.Kernel.Expr .anon
  view : FEnv .anon

def Snapshot.before (s : Snapshot) : Env .anon := s.view.env.prefixTo s.counter

/-- An accessor of the existing receipt, with no check or annotation replay.
The discarded annotated proof is not a field of this executable snapshot. -/
def snapshot (r : Receipt) (i : Nat) : Except String Snapshot := do
  let some d := r.ds[i]? | throw "theorem snapshot: declaration index is unavailable"
  let .thmDecl cv raw := d | throw "theorem snapshot: declaration is not a theorem"
  let some (counter, c) := r.index.idx[cv.name]? | throw "theorem snapshot: theorem index entry is unavailable"
  let .thmInfo stored _ := c | throw "theorem snapshot: indexed constant is not a theorem"
  return ⟨i, cv, raw, counter, stored.type, r.index.restrictTo counter⟩

theorem snapshot_of_check (V : Type w) [SetTheory V] {binding limits records blobs hint r}
    (run : checkReceipt binding limits records blobs hint = .ok r)
    {i : Nat} {cv : Ix.Kernel.ConstantVal .anon} {raw : Ix.Kernel.Expr .anon}
    (atDecl : r.ds.toList[i]? = some (.thmDecl cv raw)) :
    ∃ F before expected checkedProof,
      let snap : Snapshot := ⟨i, cv, raw, before.consts.length, expected,
        r.index.restrictTo before.consts.length⟩
      TheoremFrontAt r.ev r.ds.toList r.env i cv raw F before expected checkedProof ∧
      snapshot r i = .ok snap ∧ snap.before = before ∧ snap.view.env = r.env ∧
      (∀ n, snap.view.find? n = before.find? n) ∧ snap.view.find? cv.name = none := by
  obtain ⟨_, _, _, checkedRun, canonical⟩ := checkReceipt_ok run
  obtain ⟨F, before, expected, checkedProof, front, counter, logical, _, lookup, hidden⟩ :=
    checked_context V checkedRun atDecl
  have indexed : r.index.idx[cv.name]? = some (before.consts.length,
      .thmInfo ⟨cv.name, cv.levelParams, expected⟩ raw) := by rw [canonical]; exact counter
  have atArray : r.ds[i]? = some (.thmDecl cv raw) := by simpa using atDecl
  refine ⟨F, before, expected, checkedProof, front, ?_, ?_, rfl, ?_, ?_⟩
  · simp [snapshot, atArray, indexed, pure, Except.pure]
  · exact logical
  · intro n; rw [canonical]; exact lookup n
  · rw [canonical]; exact hidden

/-- One preparation recovered from this very receipt, including its exact
prepared declaration stream. No reader/checker is run by the proof. -/
theorem prepared_of_receipt {binding limits records blobs hint r}
    (run : checkReceipt binding limits records blobs hint = .ok r) :
    ∃ p : Prepared binding limits records blobs hint r.env,
      p.table = r.table ∧ p.pre = r.pre ∧ p.ev = r.ev ∧
      Frontend.preparePrelude p.pre.ix p.decls = r.ds := by
  have bytes : Ixon.Authenticated.checkBytes binding limits records blobs hint = .ok r.env := by
    rw [← DefinitionSnapshots.checkReceipt_env, run]; rfl
  obtain ⟨p⟩ := prepared_of_check bytes
  obtain ⟨admitted, prelude, prepared, _, _⟩ := checkReceipt_ok run
  have table := Except.ok.inj (p.admitted.symm.trans admitted)
  have pre : p.pre = r.pre := Except.ok.inj ((table ▸ p.prelude).symm.trans prelude)
  have pair := Prod.mk.inj (Except.ok.inj ((pre ▸ p.prepared).symm.trans prepared))
  exact ⟨p, table, pre, pair.1, by simpa only [pre] using pair.2⟩

variable {binding : Binding} {limits : Limits} {records : Records} {blobs : Ingress.Blobs}
  {hint : ConstRef Address → Option ReducibilityHint} {envA : Env .anon}

/-- Exact canonical theorem occurrence, actual projection rewrite, and the
same prepared theorem front. Reader and checker prefixes remain distinct. -/
def TheoremAt (p : Prepared binding limits records blobs hint envA) (j : Nat)
    (a : Address) (c : Ixon.Constant) (d : Ixon.Definition) : Prop :=
  let cx := streamContext Address.admissionHash p.table p.pre p.constants blobs hint
  ∃ fin st r key ty value i F before expected checkedProof,
    StreamRead cx p.pre.state p.constants fin p.decls ∧
    p.ev = evidenceOf cx fin p.table ∧ State.keepsPrelude p.pre.state fin = true ∧
    RecordAt cx p.pre.state fin p.constants p.decls j a c st r ∧
    cx.memberKey (.member a 0) = .ok key ∧
    (definitionReader cx a c d).read d.typ = .ok ty ∧
    (definitionReader cx a c d).read d.value = .ok value ∧
    let cv := (⟨key, singletonLps d.lvls, ty⟩ : Ix.Kernel.ConstantVal .anon)
    let raw := (projRewrite st cv value).getD value
    r.decls = #[.thmDecl cv raw] ∧
    TheoremFrontAt p.ev (Frontend.preparePrelude p.pre.ix p.decls).toList envA
      i cv raw F before expected checkedProof

theorem singleton_theorem (V : Type w) [SetTheory V]
    (p : Prepared binding limits records blobs hint envA) {j a c d}
    (atRecord : p.constants[j]? = some (a, c)) (info : c.info = .defn d) (kind : d.kind = .thm) :
    TheoremAt p j a c d := by
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
    | thm =>
      let cv : Ix.Kernel.ConstantVal .anon := ⟨key, singletonLps d.lvls, ty⟩
      let raw := (projRewrite st cv value).getD value
      have member : .thmDecl cv raw ∈ p.decls := by simp [shape, decls, cv, raw]
      have kept := Frontend.mem_preparePrelude (pre := p.pre.ix) member
      obtain ⟨i, atDecl⟩ := List.mem_iff_getElem?.mp (Array.mem_toList_iff.mpr kept)
      obtain ⟨F, before, expected, checkedProof, front⟩ := reference_theorem_front_at
        (Cached.checkDecls_refines_ref V rfl p.checked) atDecl
      exact ⟨fin, st, r, key, ty, value, i, F, before, expected, checkedProof, stream, evidence, keeps,
        ⟨atRecord, pref, suff, beforeRun, recordRun, afterRun, shape⟩, keyed, type, body, decls, front⟩
  | axio found => rw [info] at found; cases found
  | quot found => rw [info] at found; cases found

/-- All selected occurrences share this receipt's preparation. The derived
indices therefore feed snapshot_of_check without a preparation premise. -/
theorem selected_theorem_fronts (V : Type w) [SetTheory V] {binding limits ixe order receipt}
    (nodes : Ix.Map Ix.Name Ix.Compile.SourceGraph.Node) (cs : Ix.Compile.ChangedSet.ChangedSet)
    (run : checkReceipt binding limits (recordsOf ixe order) (blobsOf ixe order) (hintsOf ixe) = .ok receipt) :
    ∃ p : Prepared binding limits (recordsOf ixe order) (blobsOf ixe order) (hintsOf ixe) receipt.env,
      p.table = receipt.table ∧ p.pre = receipt.pre ∧ p.ev = receipt.ev ∧
      Frontend.preparePrelude p.pre.ix p.decls = receipt.ds ∧
      ∀ r ∈ SourcePublication.selectOriginal nodes cs ixe, ∀ j bytes,
        (recordsOf ixe order)[j]? = some (r.address, bytes) →
        ∃ c, p.constants[j]? = some (r.address, c) ∧
          Ixon.Verify.Canonical.Reads limits.maxRecordBytes limits.maxRecordUnivNodes bytes c ∧
          ∀ d, c.info = .defn d → d.kind = .thm → TheoremAt p j r.address c d := by
  obtain ⟨p, table, pre, ev, ds⟩ := prepared_of_receipt run
  refine ⟨p, table, pre, ev, ds, fun r _ j bytes atByte => ?_⟩
  obtain ⟨c, atRecord, read⟩ := decoded_at (decodeRecords_ok_iff .. |>.mp p.decoded) atByte
  exact ⟨c, atRecord, read, fun d info kind => singleton_theorem V p atRecord info kind⟩

end Ix.Cert.TheoremSnapshots
