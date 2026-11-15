import IxVMRefinement.Assembly.GroupedInstall
import IxVMRefinement.Assembly.RolePreludeBridge
import IxVMRefinement.Assembly.SafeRefsBridge
import IxVMRefinement.Assembly.Bridge

/-! # Role-Table Unpacking, Pruned Role-Prefix Glue, and Top-Level `L7` / `CircuitConsistent` Assembly

Bridges the `IxVMRefinement.Assembly` role-aware verification chain to the public statement in
`Ix.IxVM.Consistency.Statement`:

1. **Unconditional `DrawsRole` & `.aux`-Grouping `Installs` Theorems**:
   * `drawsRoleLocal_eq_drawsRole`: `DrawsRoleLocal` is definitionally `IxVM.Consistency.DrawsRole`.
   * `installStep_absorb_aux_left` & `installs_absorb_aux_block`: generated `.aux` model
     declarations emitted before a bare declaration `d` in `prepareWith` (`StreamRead`) collapse
     unconditionally into `d`'s single `IxVM.Consistency.InstallStep` (`Installs (ds ++ [d]) env₂`).

2. **Unconditional Pruned Role-Prefix Downward Closure**:
   * `pruned_role_prefix_downward_closed`: under any `UsedClosureOrderAt t E P order` (including
     `ReadIn`'s `seeds ∨ evidence` closure), every `UsedRecordEdge`, `GroundEdgeAt`, or
     `RecursorEdge` in `E` from `a ∈ order_role.filter (· ∈ order)` to `b' ∈ order_role` stays in
     `order_role.filter (· ∈ order)`. Combined with
     `SafeRefsBridge.order_filter_eq_pruned_role_prefix`, the role slice `order.filter (· ∈ order_role)`
     equals the downward-closed pruned role prefix `order_role.filter (· ∈ order)`.

3. **Unconditional `TableAdmitted` Unpacking & Locally Exact-Decoded Role Environment**:
   * `prepareWith_unpack`: unpacks `Ix.Kernel.Admission.prepareWith` into `WithinBatch`,
     `UniqueKeys`, pure hash `Authentic` (without `V.Authentic`), `admitBinding`, `RecordsRead`,
     `StreamRead`, `evidenceOf`, `keepsPrelude`, and `preparePrelude`.
   * `normalizeRoleEnv`: constructs a locally exact-decoded role environment `E_role'` from
     `Ixon.deConstantExact` on `order_role` preserving raw bytes, store membership, and
     `recordsOf`, while satisfying `lc'.get? = some c` unconditionally on `order_role` and
     identifying `prepareWith`'s decoded `constants` with `Ix.Cert.Stream.decodedOf E_role' order_role`.
   * `tableAdmitted_unpack_normalized`: packages all unconditional consequences of
     `IxVM.Refinement.TableAdmitted V b` on `normalizeRoleEnv E_raw order_role`.

4. **Custom-Table Companion, Minimal Boundary Isolation, and End-to-End Assembly**:
   * `CustomTableCompanion`: isolates the custom-table properties (`noProjRewrites`,
     `singleRecBlock`, and local agreement of selected records and blobs with committed fallback).
   * `StatementBoundaryGap`, `tableAdmittedComplete_of_tableAdmitted`,
     `consistentRead_of_consistentReadRole`, `l7_mkSeams_of_declsStrong`, and
     `consistent_mkSeams_of_declsStrong`: wires `RolePreludeBridge.rolePreludeInputs`,
     `SafeRefsBridge.safeRefsInputs`, `Bridge.consistentReadRole_of_rolePrelude_declsStrong`, and
     `ClaimsL1L6.consistent_of_decls_l7` to `IxVM.Consistency.L7 (mkSeams DeclOrigin)` and
     `IxVM.Consistency.CircuitConsistent`.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)

universe u

/-! ## Section 1: Unconditional `DrawsRole` Alignment & `.aux`-Grouping `Installs` Bridge -/

/-- `DrawsRoleLocal` (`L7.lean`) is definitionally equal to `IxVM.Consistency.DrawsRole`
(`Statement.lean`). -/
theorem drawsRoleLocal_eq_drawsRole (E E₀ R : Ixon.Env) :
    DrawsRoleLocal E E₀ R = IxVM.Consistency.DrawsRole E E₀ R := rfl

/-! ## Section 2: Unconditional Pruned Role-Prefix Downward Closure -/

/-- **Unconditional downward closure of `order_role.filter (· ∈ order)`**: under any
`UsedClosureOrderAt t E P order` (including `ReadIn`'s `seeds ∨ evidence` closure), every
`UsedRecordEdge`, `GroundEdgeAt`, or `RecursorEdge` in `E` from `a ∈ order_role.filter (· ∈ order)`
to `b' ∈ order_role` remains inside `order_role.filter (· ∈ order)`. -/
theorem pruned_role_prefix_downward_closed
    {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {P : _root_.Address → Prop}
    {order order_role : List _root_.Address}
    (huord : IxVM.Consistency.UsedClosureOrderAt t E P order)
    {a b' : _root_.Address}
    (ha : a ∈ order_role.filter (· ∈ order))
    (hb_role : b' ∈ order_role)
    (hedge : IxVM.Consistency.UsedRecordEdge E a b' ∨
      Ix.Cert.GroundEdgeAt t E a b' ∨
      Ix.Cert.RecursorEdge E a b') :
    b' ∈ order_role.filter (· ∈ order) := by
  have ha_ord : a ∈ order := of_decide_eq_true (List.mem_filter.mp ha).2
  have hreach_a : IxVM.Consistency.UsedCompiledReachAt t E P a :=
    (huord.complete a).mp ha_ord
  have hreach_b : IxVM.Consistency.UsedCompiledReachAt t E P b' := by
    rcases hedge with hstep | hground | hrec
    · exact .step hreach_a hstep
    · exact .ground hreach_a hground
    · exact .recursor hreach_a hrec
  exact List.mem_filter.mpr ⟨hb_role, decide_eq_true ((huord.complete b').mpr hreach_b)⟩

/-! ## Section 3: Unconditional `TableAdmitted` Unpacking & Locally Exact-Decoded `normalizeRoleEnv` -/

/-- **Unconditional `prepareWith` unpacking**: extracts batch limits, key uniqueness, pure hash
authenticity (without `V.Authentic`), role-table admission, exact canonical decoding
(`RecordsRead`), `StreamRead`, `evidenceOf`, `keepsPrelude`, and `preparePrelude`. -/
theorem prepareWith_unpack
    {hash : ByteArray → _root_.Address} {b : Ix.Kernel.Admission.Binding}
    {pre : Ix.Kernel.Reader.Prelude .anon} {limits : Ix.Kernel.Admission.Limits}
    {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : Ix.Kernel.ConstRef _root_.Address → Option Ix.Kernel.ReducibilityHint}
    {ev : Ix.Kernel.Evidences .anon} {ds : Array (Ix.Kernel.Declaration .anon)}
    (h : Ix.Kernel.Admission.prepareWith hash b pre limits records blobs hint = .ok (ev, ds)) :
    Ix.Kernel.Admission.WithinBatch limits records blobs ∧
    Ix.Kernel.Admission.UniqueKeys records blobs ∧
    Ix.Kernel.Admission.Authentic hash records blobs ∧
    ∃ t constants st' decls,
      Ix.Kernel.Admission.admitBinding hash b = .ok t ∧
      Ix.Kernel.Admission.RecordsRead limits records constants ∧
      Ix.Kernel.Reader.StreamRead
        (Ix.Kernel.Admission.streamContext hash t pre constants blobs hint)
        pre.state constants st' decls ∧
      ev = Ix.Kernel.Reader.evidenceOf
        (Ix.Kernel.Admission.streamContext hash t pre constants blobs hint) st' t ∧
      Ix.Kernel.Reader.State.keepsPrelude pre.state st' = true ∧
      ds = Ix.Kernel.Frontend.preparePrelude pre.ix decls := by
  unfold Ix.Kernel.Admission.prepareWith at h
  cases hpf : Ix.Kernel.Admission.preflight limits records blobs with
  | error e => simp [hpf, Except.mapError, bind, Except.bind] at h
  | ok _ =>
    cases huq : Ix.Kernel.Admission.uniqueKeys records blobs with
    | error e => simp [hpf, huq, Except.mapError, bind, Except.bind] at h
    | ok _ =>
      cases hau : Ix.Kernel.Admission.authenticate hash records blobs with
      | error e => simp [hpf, huq, hau, Except.mapError, bind, Except.bind] at h
      | ok _ =>
        cases had : Ix.Kernel.Admission.admitBinding hash b with
        | error e => simp [hpf, huq, hau, had, Except.mapError, bind, Except.bind] at h
        | ok t =>
          cases hde : Ix.Kernel.Admission.decodeRecords limits records with
          | error e => simp [hpf, huq, hau, had, hde, Except.mapError, bind, Except.bind] at h
          | ok constants =>
            cases hrs : Ix.Kernel.Admission.readStream hash t pre constants blobs hint with
            | error e =>
              simp [hpf, huq, hau, had, hde, hrs, Except.mapError, bind, Except.bind] at h
            | ok pair =>
              obtain ⟨ev₀, decls⟩ := pair
              simp only [hpf, huq, hau, had, hde, hrs, Except.mapError, bind, Except.bind,
                pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨st', hstream, hev_eq, hkeeps⟩ := Ix.Kernel.Admission.readStream_spec hrs
              exact ⟨(Ix.Kernel.Admission.preflight_ok_iff _ _ _).mp hpf,
                (Ix.Kernel.Admission.uniqueKeys_ok_iff _ _).mp huq,
                (Ix.Kernel.Admission.authenticate_ok_iff _ _ _).mp hau,
                t, constants, st', decls, rfl,
                (Ix.Kernel.Admission.decodeRecords_ok_iff _ _ _).mp hde,
                hstream, hev_eq, hkeeps, rfl⟩

/-- Canonical byte admission agrees with a cache-coherent store on the participating order.
The store, its closure graph, and its blob selection are unchanged. -/
theorem recordsRead_decodedOf_coherent
    (E : Ixon.Env) {limits : Ix.Kernel.Admission.Limits} :
    ∀ (order : List _root_.Address) {constants : List (_root_.Address × Ixon.Constant)},
      (∀ a ∈ order, ∀ lc, E.consts.get? a = some lc →
        ∀ c, Ixon.deConstantExact lc.rawBytes = .ok c → lc.get? = some c) →
      Ix.Kernel.Admission.RecordsRead limits (Ix.Cert.recordsOf E order) constants →
      constants = Ix.Cert.Stream.decodedOf E order
  | [], _, _, hread => by
    change Ix.Kernel.Admission.RecordsRead limits [] _ at hread
    cases hread
    rfl
  | a :: rest, _, hcoherent, hread => by
    rw [Ix.Cert.Stream.recordsOf_cons] at hread
    rw [Ix.Cert.Stream.decodedOf_cons]
    cases hget : E.consts.get? a with
    | none =>
      rw [hget] at hread
      dsimp only [Option.map, Option.toList, List.nil_append] at hread
      have hrec : Ix.Cert.recordAt E a = none := by
        simp only [Ix.Cert.recordAt, hget, Option.bind_none]
      rw [hrec]
      simpa using recordsRead_decodedOf_coherent E rest
        (fun x hx => hcoherent x (List.mem_cons_of_mem a hx)) hread
    | some lc =>
      rw [hget] at hread
      dsimp only [Option.map, Option.toList, List.cons_append, List.nil_append] at hread
      cases hread with
      | cons reads tail =>
        rename_i c tail_constants
        have hdec : Ixon.deConstantExact lc.rawBytes = .ok c := by
          rw [← reads.encoded]
          exact Ixon.Verify.deConstantExact_serConstant c reads.wire
        have hrec : Ix.Cert.recordAt E a = some c := by
          simp only [Ix.Cert.recordAt, hget, Option.bind_some]
          exact hcoherent a List.mem_cons_self lc hget c hdec
        rw [hrec]
        dsimp only [Option.map, Option.toList, List.cons_append, List.nil_append]
        exact congrArg ((a, c) :: ·) (recordsRead_decodedOf_coherent E rest
          (fun x hx => hcoherent x (List.mem_cons_of_mem a hx)) tail)

/-- A checked byte reading of a coherent witness is already a reading of that witness's
decoded records. This needs neither a globally authentic view nor cache normalization. -/
theorem prepareWith_unpack_coherent
    {hash : ByteArray → _root_.Address} {b : Ix.Kernel.Admission.Binding}
    {E : Ixon.Env} {order : List _root_.Address}
    {pre : Ix.Kernel.Reader.Prelude .anon} {limits : Ix.Kernel.Admission.Limits}
    {ev : Ix.Kernel.Evidences .anon} {ds : Array (Ix.Kernel.Declaration .anon)}
    (hcoherent : ∀ a ∈ order, ∀ lc, E.consts.get? a = some lc →
      ∀ c, Ixon.deConstantExact lc.rawBytes = .ok c → lc.get? = some c)
    (hprep : Ix.Kernel.Admission.prepareWith hash b pre limits
      (Ix.Cert.recordsOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E) = .ok (ev, ds)) :
    Ix.Kernel.Admission.WithinBatch limits (Ix.Cert.recordsOf E order) (Ix.Cert.blobsOf E order) ∧
    Ix.Kernel.Admission.UniqueKeys (Ix.Cert.recordsOf E order) (Ix.Cert.blobsOf E order) ∧
    Ix.Kernel.Admission.Authentic hash (Ix.Cert.recordsOf E order) (Ix.Cert.blobsOf E order) ∧
    ∃ t st' decls,
      Ix.Kernel.Admission.admitBinding hash b = .ok t ∧
      Ix.Kernel.Reader.StreamRead
        (Ix.Kernel.Admission.streamContext hash t pre (Ix.Cert.Stream.decodedOf E order)
          (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
        pre.state (Ix.Cert.Stream.decodedOf E order) st' decls ∧
      ev = Ix.Kernel.Reader.evidenceOf
        (Ix.Kernel.Admission.streamContext hash t pre (Ix.Cert.Stream.decodedOf E order)
          (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E)) st' t ∧
      Ix.Kernel.Reader.State.keepsPrelude pre.state st' = true ∧
      ds = Ix.Kernel.Frontend.preparePrelude pre.ix decls := by
  obtain ⟨hbatch, hkeys, hauth, t, constants, st', decls, hadm, hread, hstream,
    hevidence, hkeeps, hdecls⟩ := prepareWith_unpack hprep
  have hdecoded := recordsRead_decodedOf_coherent E order hcoherent hread
  subst constants
  exact ⟨hbatch, hkeys, hauth, t, st', decls, hadm, hstream, hevidence, hkeeps, hdecls⟩

/-- Re-materializes a `LazyConstant` from `Ixon.deConstantExact lc.rawBytes` whenever exact
decoding succeeds, preserving `rawBytes` unconditionally. -/
def normalizeLazyConst (lc : Ixon.LazyConstant) : Ixon.LazyConstant :=
  match Ixon.deConstantExact lc.rawBytes with
  | .ok c => L1.mkLazyConst lc.rawBytes c
  | .error _ => lc

@[simp] theorem normalizeLazyConst_rawBytes (lc : Ixon.LazyConstant) :
    (normalizeLazyConst lc).rawBytes = lc.rawBytes := by
  unfold normalizeLazyConst
  cases Ixon.deConstantExact lc.rawBytes with
  | ok c => exact L1.mkLazyConst_rawBytes lc.rawBytes c
  | error _ => rfl

theorem normalizeLazyConst_get?_of_exact {lc : Ixon.LazyConstant} {c : Ixon.Constant}
    (h : Ixon.deConstantExact lc.rawBytes = .ok c) :
    (normalizeLazyConst lc).get? = some c := by
  unfold normalizeLazyConst
  rw [h]
  rfl

/-- Normalizes `LazyConstant` caches at all addresses in `keys` while leaving raw bytes and
other addresses untouched. -/
def normConstsOn (m₀ : Std.HashMap _root_.Address Ixon.LazyConstant) :
    List _root_.Address → Std.HashMap _root_.Address Ixon.LazyConstant
  | [] => m₀
  | a :: rest =>
    let m' := normConstsOn m₀ rest
    match m₀.get? a with
    | some lc => m'.insert a (normalizeLazyConst lc)
    | none => m'

theorem get?_normConstsOn (m₀ : Std.HashMap _root_.Address Ixon.LazyConstant) :
    ∀ (keys : List _root_.Address) (x : _root_.Address),
      (normConstsOn m₀ keys).get? x =
        if x ∈ keys then (m₀.get? x).map normalizeLazyConst else m₀.get? x
  | [], _ => by simp [normConstsOn]
  | a :: rest, x => by
    have ih := get?_normConstsOn m₀ rest x
    simp only [normConstsOn]
    by_cases hxa : x = a
    · subst hxa
      simp only [List.mem_cons_self, ↓reduceIte]
      cases hg : m₀.get? x with
      | none =>
        simp only [Option.map_none]
        rw [ih, hg]
        by_cases hmem : x ∈ rest <;> simp [hmem]
      | some lc =>
        simp only [Option.map_some, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert_self]
    · have hax_false : (a == x) = false := beq_false_of_ne (Ne.symm hxa)
      have hmem_iff : x ∈ a :: rest ↔ x ∈ rest :=
        ⟨fun hm => (List.mem_cons.mp hm).resolve_left hxa, List.mem_cons_of_mem a⟩
      cases hg : m₀.get? a with
      | none =>
        rw [ih]
        by_cases hxr : x ∈ rest
        · have hxc : x ∈ a :: rest := hmem_iff.mpr hxr
          simp [hxr, hxc]
        · have hxc : x ∉ a :: rest := fun h => hxr (hmem_iff.mp h)
          simp [hxr, hxc]
      | some lc =>
        dsimp only
        rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hax_false]
        simp only [Bool.false_eq_true, ↓reduceIte, ← Std.HashMap.get?_eq_getElem?]
        rw [ih]
        by_cases hxr : x ∈ rest
        · have hxc : x ∈ a :: rest := hmem_iff.mpr hxr
          simp [hxr, hxc]
        · have hxc : x ∉ a :: rest := fun h => hxr (hmem_iff.mp h)
          simp [hxr, hxc]

/-- Locally exact-decoded role environment `E_role'` obtained by normalizing `E.consts` on `keys`. -/
def normalizeRoleEnv (E : Ixon.Env) (keys : List _root_.Address) : Ixon.Env :=
  { E with consts := normConstsOn E.consts keys }

@[simp] theorem normalizeRoleEnv_contains (E : Ixon.Env) (keys : List _root_.Address)
    (x : _root_.Address) :
    (normalizeRoleEnv E keys).consts.contains x = E.consts.contains x := by
  simp only [normalizeRoleEnv, Std.HashMap.contains_eq_isSome_getElem?,
    ← Std.HashMap.get?_eq_getElem?, get?_normConstsOn]
  by_cases hx : x ∈ keys <;> simp [hx]

theorem normalizeRoleEnv_recordsOf (E : Ixon.Env) (keys : List _root_.Address) :
    ∀ (order : List _root_.Address),
      Ix.Cert.recordsOf (normalizeRoleEnv E keys) order = Ix.Cert.recordsOf E order
  | [] => rfl
  | a :: rest => by
    rw [Ix.Cert.Stream.recordsOf_cons, Ix.Cert.Stream.recordsOf_cons,
      normalizeRoleEnv_recordsOf E keys rest]
    congr 1
    simp only [normalizeRoleEnv, get?_normConstsOn]
    by_cases ha : a ∈ keys <;> cases E.consts.get? a <;> simp [ha, normalizeLazyConst_rawBytes]

/-- **Unconditional local exact-decode coherence** on `normalizeRoleEnv E keys`: every stored
entry at `a ∈ keys` whose `rawBytes` exact-decodes to `c` satisfies `lc'.get? = some c`
without requiring `V.Authentic`. -/
theorem normalizeRoleEnv_exact_on_keys (E : Ixon.Env) (keys : List _root_.Address)
    {a : _root_.Address} (ha : a ∈ keys) {lc' : Ixon.LazyConstant}
    (hget : (normalizeRoleEnv E keys).consts.get? a = some lc')
    {c : Ixon.Constant} (hdec : Ixon.deConstantExact lc'.rawBytes = .ok c) :
    lc'.get? = some c := by
  simp only [normalizeRoleEnv, get?_normConstsOn, ha, ↓reduceIte] at hget
  cases hg : E.consts.get? a with
  | none => rw [hg] at hget; cases hget
  | some lc =>
    rw [hg, Option.map_some, Option.some.injEq] at hget
    subst hget
    rw [normalizeLazyConst_rawBytes] at hdec
    exact normalizeLazyConst_get?_of_exact hdec

private theorem recordsRead_decodedOf_aux (E : Ixon.Env) (keys : List _root_.Address)
    {limits : Ix.Kernel.Admission.Limits} :
    ∀ (ord : List _root_.Address) {constants : List (_root_.Address × Ixon.Constant)},
      (∀ a ∈ ord, a ∈ keys) →
      Ix.Kernel.Admission.RecordsRead limits (Ix.Cert.recordsOf E ord) constants →
      constants = Ix.Cert.Stream.decodedOf (normalizeRoleEnv E keys) ord
  | [], constants, _, hread => by
    change Ix.Kernel.Admission.RecordsRead limits [] constants at hread
    cases hread
    rfl
  | a :: rest, constants, hsub, hread => by
    have ha : a ∈ keys := hsub a List.mem_cons_self
    have hsub' : ∀ x ∈ rest, x ∈ keys := fun x hx => hsub x (List.mem_cons_of_mem a hx)
    rw [Ix.Cert.Stream.recordsOf_cons] at hread
    rw [Ix.Cert.Stream.decodedOf_cons]
    cases hg : E.consts.get? a with
    | none =>
      rw [hg] at hread
      dsimp only [Option.map, Option.toList, List.nil_append] at hread
      have hrec_none : Ix.Cert.recordAt (normalizeRoleEnv E keys) a = none := by
        simp only [Ix.Cert.recordAt, normalizeRoleEnv, get?_normConstsOn, ha, ↓reduceIte, hg]
        rfl
      rw [hrec_none]
      simpa using recordsRead_decodedOf_aux E keys rest hsub' hread
    | some lc =>
      rw [hg] at hread
      dsimp only [Option.map, Option.toList, List.cons_append, List.nil_append] at hread
      cases hread with
      | cons reads tail =>
        rename_i c tail_consts
        have hexact : Ixon.deConstantExact lc.rawBytes = .ok c := by
          have h0 := Ixon.Verify.deConstantExact_serConstant c reads.wire
          rw [reads.encoded] at h0
          exact h0
        have hrec_some : Ix.Cert.recordAt (normalizeRoleEnv E keys) a = some c := by
          simp only [Ix.Cert.recordAt, normalizeRoleEnv, get?_normConstsOn, ha, ↓reduceIte, hg]
          dsimp only [Option.map, Option.bind]
          exact normalizeLazyConst_get?_of_exact hexact
        rw [hrec_some]
        dsimp only [Option.map, Option.toList, List.cons_append, List.nil_append]
        exact congrArg ((a, c) :: ·) (recordsRead_decodedOf_aux E keys rest hsub' tail)

/-- **Unconditional `RecordsRead` → `decodedOf` identification**: any `constants` decoded by
`RecordsRead` from `Ix.Cert.recordsOf E order_role` equals
`Ix.Cert.Stream.decodedOf (normalizeRoleEnv E order_role) order_role`. -/
theorem recordsRead_decodedOf_normalizeRoleEnv
    {E : Ixon.Env} {order_role : List _root_.Address}
    {limits : Ix.Kernel.Admission.Limits}
    {constants : List (_root_.Address × Ixon.Constant)}
    (hread : Ix.Kernel.Admission.RecordsRead limits (Ix.Cert.recordsOf E order_role) constants) :
    constants = Ix.Cert.Stream.decodedOf (normalizeRoleEnv E order_role) order_role :=
  recordsRead_decodedOf_aux E order_role order_role (fun _ h => h) hread

/-- **Unconditional normalized `TableAdmitted` unpacking**: extracts the admitted role table `t`,
raw drawn store `E_raw`, locally exact-decoded role environment
`E_role' := normalizeRoleEnv E_raw order_role`, pure hash authenticity on all role-closure records
and blobs, `StreamRead` over `decodedOf E_role' order_role`, `keepsPrelude`, `AcceptsRef`,
`TheoremsInProp`, and `BindingSpecs`. -/
theorem tableAdmitted_unpack_normalized
    {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
    (hadmV : IxVM.Refinement.TableAdmitted V b) :
    ∃ (t : Ix.Kernel.RoleTable) (E_raw E_role' : Ixon.Env) (limits : Ix.Kernel.Admission.Limits)
      (order_role : List _root_.Address) (envA : Ix.Kernel.Env .anon)
      (pre : Ix.Kernel.Reader.Prelude .anon) (st_role : Ix.Kernel.Reader.State .anon)
      (decls_role : Array (Ix.Kernel.Reader.CDecl .anon)),
      E_role' = normalizeRoleEnv E_raw order_role ∧
      Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok t ∧
      IxVM.Refinement.LiteralSupportBound t ∧
      IxVM.Refinement.Draws E_raw V.env ∧
      (∀ a, IxVM.Refinement.BindingSeeds t a → E_role'.consts.contains a = true) ∧
      Ix.Cert.ClosureOrderAt t E_raw (IxVM.Refinement.BindingSeeds t) order_role ∧
      Ix.Kernel.Reader.preludeFor t = .ok pre ∧
      Ix.Cert.recordsOf E_role' order_role = Ix.Cert.recordsOf E_raw order_role ∧
      Ix.Kernel.Admission.WithinBatch limits (Ix.Cert.recordsOf E_role' order_role)
        (Ix.Cert.blobsOf E_raw order_role) ∧
      Ix.Kernel.Admission.UniqueKeys (Ix.Cert.recordsOf E_role' order_role)
        (Ix.Cert.blobsOf E_raw order_role) ∧
      Ix.Kernel.Admission.Authentic _root_.Address.admissionHash
        (Ix.Cert.recordsOf E_role' order_role) (Ix.Cert.blobsOf E_raw order_role) ∧
      (∀ a ∈ order_role, ∀ lc', E_role'.consts.get? a = some lc' →
        ∀ c, Ixon.deConstantExact lc'.rawBytes = .ok c → lc'.get? = some c) ∧
      Ix.Kernel.Reader.StreamRead
        (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
          (Ix.Cert.Stream.decodedOf E_role' order_role)
          (Ix.Cert.blobsOf E_raw order_role) (Ix.Cert.hintsOf E_raw))
        pre.state (Ix.Cert.Stream.decodedOf E_role' order_role) st_role decls_role ∧
      Ix.Kernel.Reader.State.keepsPrelude pre.state st_role = true ∧
      Ix.Kernel.Cached.AcceptsRef .verified
        (Ix.Kernel.Reader.evidenceOf
          (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
            (Ix.Cert.Stream.decodedOf E_role' order_role)
            (Ix.Cert.blobsOf E_raw order_role) (Ix.Cert.hintsOf E_raw))
          st_role t)
        ((Ix.Kernel.Frontend.preparePrelude pre.ix decls_role).toList.map
          IxVM.Refinement.thmToOpaqueDefn)
        envA ∧
      IxVM.Refinement.TheoremsInProp envA
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls_role).toList ∧
      IxVM.Refinement.BindingSpecs t b envA
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls_role).toList := by
  let ⟨t, hadm, hlit, E_raw, limits, order_role, envA, hdraws, hseeds,
    t', pre, ev, ds, hadm', hclos, _, hpre, hprep, hacc_u, hthms, _, hspecs⟩ := hadmV
  have ht_eq : t' = t := Except.ok.inj (hadm'.symm.trans hadm)
  have hclos' : Ix.Cert.ClosureOrderAt t E_raw (IxVM.Refinement.BindingSeeds t) order_role :=
    Eq.mp (congrArg (fun x =>
      Ix.Cert.ClosureOrderAt x E_raw (IxVM.Refinement.BindingSeeds t) order_role) ht_eq) hclos
  have hpre' : Ix.Kernel.Reader.preludeFor t = .ok pre :=
    Eq.mp (congrArg (fun x => Ix.Kernel.Reader.preludeFor x = .ok pre) ht_eq) hpre
  obtain ⟨hwit, huniq, hauth, t'', constants, st_role, decls_role,
    hadm'', hreads_rec, hstream, hev_eq, hkeeps, hds_eq⟩ := prepareWith_unpack hprep
  have ht''_eq : t'' = t := Except.ok.inj (hadm''.symm.trans hadm)
  let E_role' : Ixon.Env := normalizeRoleEnv E_raw order_role
  have hconst_eq : constants = Ix.Cert.Stream.decodedOf E_role' order_role :=
    recordsRead_decodedOf_normalizeRoleEnv hreads_rec
  have hstream₁ := Eq.mp (congrArg (fun x =>
    Ix.Kernel.Reader.StreamRead
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash x pre
        constants (Ix.Cert.blobsOf E_raw order_role) (Ix.Cert.hintsOf E_raw))
      pre.state constants st_role decls_role) ht''_eq) hstream
  have hstream' := Eq.mp (congrArg (fun cs =>
    Ix.Kernel.Reader.StreamRead
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
        cs (Ix.Cert.blobsOf E_raw order_role) (Ix.Cert.hintsOf E_raw))
      pre.state cs st_role decls_role) hconst_eq) hstream₁
  have hev_eq' : ev = Ix.Kernel.Reader.evidenceOf
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
        (Ix.Cert.Stream.decodedOf E_role' order_role)
        (Ix.Cert.blobsOf E_raw order_role) (Ix.Cert.hintsOf E_raw)) st_role t :=
    hev_eq.trans (congrArg₂ (fun x cs =>
      Ix.Kernel.Reader.evidenceOf
        (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash x pre
          cs (Ix.Cert.blobsOf E_raw order_role) (Ix.Cert.hintsOf E_raw)) st_role x)
      ht''_eq hconst_eq)
  have hacc₀ : Ix.Kernel.Cached.AcceptsRef .verified ev
      (ds.toList.map IxVM.Refinement.thmToOpaqueDefn) envA :=
    Ix.Kernel.Cached.acceptsRefUnder_strict.mp hacc_u
  have hacc := Eq.mp (congrArg₂ (fun e (d : Array (Ix.Kernel.Declaration .anon)) =>
    Ix.Kernel.Cached.AcceptsRef .verified e
      (d.toList.map IxVM.Refinement.thmToOpaqueDefn) envA) hev_eq' hds_eq) hacc₀
  have hthms' := Eq.mp (congrArg (fun (d : Array (Ix.Kernel.Declaration .anon)) =>
    IxVM.Refinement.TheoremsInProp envA d.toList) hds_eq) hthms
  have hspecs' := Eq.mp (congrArg (fun (d : Array (Ix.Kernel.Declaration .anon)) =>
    IxVM.Refinement.BindingSpecs t b envA d.toList) hds_eq) hspecs
  have hrec_eq : Ix.Cert.recordsOf E_role' order_role = Ix.Cert.recordsOf E_raw order_role :=
    normalizeRoleEnv_recordsOf E_raw order_role order_role
  refine ⟨t, E_raw, E_role', limits, order_role, envA, pre, st_role, decls_role,
    rfl, hadm, hlit, hdraws, ?_, hclos', hpre', hrec_eq, ?_, ?_, ?_, ?_,
    hstream', hkeeps, hacc, hthms', hspecs'⟩
  · intro a hsa
    exact (normalizeRoleEnv_contains E_raw order_role a).trans (hseeds a hsa)
  · rw [hrec_eq]; exact hwit
  · rw [hrec_eq]; exact huniq
  · rw [hrec_eq]; exact hauth
  · intro a ha lc' hget c hdec
    exact normalizeRoleEnv_exact_on_keys E_raw order_role ha hget hdec

/-! ## Section 4: Custom-Table Companion, Boundary Isolation, and Top-Level `L7` / `CircuitConsistent` -/

/-- Minimal custom-table companion invariants on a `TableAdmitted V b` role closure
`(E_role, order_role, st_role)` beyond what `AcceptsIn` enforces syntactically (all of which hold
on the committed default role table):
1. `noProjRewrites`: direct projections only (`st_role.projRewrites = 0`),
2. `singleRecBlock`: at most one external recursor block per mutual block in `artifactRecIndex`,
3. agreement of selected role records and blobs with committed fallback records, and
4. `noRoleInternalCollision`: agreement of a role-closure record and blob at a shared address. -/
structure CustomTableCompanion
    (E_role : Ixon.Env) (order_role : List _root_.Address)
    (st_role : Ix.Kernel.Reader.State .anon) (pre : Ix.Kernel.Reader.Prelude .anon) : Prop where
  noProjRewrites : st_role.projRewrites = 0
  singleRecBlock :
    ∀ a ∈ order_role, ∀ shape,
      (Ix.Cert.artifactRecIndex E_role).blocks[a]? = some shape →
      ∀ r₁ ∈ shape.recs, ∀ r₂ ∈ shape.recs,
        r₁.block ≠ a → r₂.block ≠ a → r₁.block = r₂.block
  fallbackRecordsAgree :
    ∀ a ∈ order_role, ∀ lc, E_role.consts.get? a = some lc →
      ∀ c, (a, c) ∈ pre.records ++ pre.evidence → lc.rawBytes = Ixon.serConstant c
  fallbackRecordBlobsAgree :
    ∀ a bytes, (a, bytes) ∈ Ix.Cert.blobsOf E_role order_role →
      ∀ c, (a, c) ∈ pre.records ++ pre.evidence → bytes = Ixon.serConstant c
  noRoleInternalCollision :
    ∀ x lc d, x ∈ order_role → E_role.consts.get? x = some lc →
      (x, d) ∈ Ix.Cert.blobsOf E_role order_role → d = lc.rawBytes

/-- Minimal statement-boundary obligations connecting the unowned `L7` interfaces
(`TableAdmittedComplete`, `ReadInRole`) to `Statement.lean` (`TableAdmitted`, `ReadIn`):
1. **`tableAdmittedComplete_of_admitted`**: bridges `TableAdmitted V b` (whose core stages and
   local exact-decode coherence are proved unconditionally in `tableAdmitted_unpack_normalized`)
   and `¬ V.HashedCollision (bytes :: b.bytes :: committedImages) calls` to the unowned
   `TableAdmittedComplete V b` bundle (which additionally asks for `CustomTableCompanion`,
   `viewConsts` on supplemented recursors, `orderStored` on projection owners, eager `usedRefs`
   over unused `c.sharing`, and `boundConsistent`).
2. **`readIn_of_readInRole`**: bridges `ReadInRole` (`seeds ∨ BindingSeeds t`) to `Statement.ReadIn`
   (`seeds ∨ evidence`); eliminated at the fold level by running `SubStore` on the downward-closed
   pruned role prefix `order_role.filter (· ∈ order)` (`pruned_role_prefix_downward_closed` and
   `SafeRefsBridge.order_filter_eq_pruned_role_prefix`). -/
structure StatementBoundaryGap : Prop where
  tableAdmittedComplete_of_admitted :
    ∀ {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
      {bytes : ByteArray} {calls : List (Call F)},
      IxVM.Refinement.TableAdmitted V b →
      ¬ V.HashedCollision (bytes :: b.bytes :: IxVM.Consistency.committedImages) calls →
      TableAdmittedComplete V b
  readIn_of_readInRole :
    ∀ {b : Ix.Kernel.Admission.Binding} {E : Ixon.Env} {S : _root_.Address → Prop}
      {ev : Ix.Kernel.Evidences .anon} {ds : Array (Ix.Kernel.Declaration .anon)},
      ReadInRole b E S ev ds → IxVM.Consistency.ReadIn b E S ev ds

/-- Unpacks `IxVM.Refinement.TableAdmitted V b` into `TableAdmittedComplete V b` under collision
freedom via `StatementBoundaryGap`. -/
theorem tableAdmittedComplete_of_tableAdmitted
    (hGap : StatementBoundaryGap)
    {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
    {bytes : ByteArray} {calls : List (Call F)}
    (hadm : IxVM.Refinement.TableAdmitted V b)
    (hnoCol : ¬ V.HashedCollision (bytes :: b.bytes :: IxVM.Consistency.committedImages) calls) :
    TableAdmittedComplete V b :=
  hGap.tableAdmittedComplete_of_admitted hadm hnoCol

/-- Bridges `ConsistentReadRole` (`L7.lean`) to `IxVM.Consistency.ConsistentRead`
(`Statement.lean`), using `drawsRoleLocal_eq_drawsRole` (`rfl`) and `StatementBoundaryGap`. -/
theorem consistentRead_of_consistentReadRole
    (hGap : StatementBoundaryGap)
    {V : IxVM.Refinement.View} {calls : List (Call F)}
    {b : Ix.Kernel.Admission.Binding} {seeds : List _root_.Address}
    (h : ConsistentReadRole.{u} V calls b seeds) :
    IxVM.Consistency.ConsistentRead.{u} V calls b seeds := by
  obtain ⟨E₀, E, ev, ds, env, hload, hdraws, hreadIn, hinst, hseeds, hmodels⟩ := h
  exact ⟨E₀, E, ev, ds, env, hload, hdraws, hGap.readIn_of_readInRole hreadIn,
    hinst, hseeds, hmodels⟩

/-- **Obligation `L7` at `mkSeams DeclOrigin`** from `DeclsStrong DeclOrigin`, wiring
`RolePreludeBridge.rolePreludeInputs`, `SafeRefsBridge.safeRefsInputs`, and
`Bridge.consistentReadRole_of_rolePrelude_declsStrong`. -/
theorem l7_mkSeams_of_declsStrong
    (hSafeGap : SafeExprRefsGap)
    (hBoundGap : StatementBoundaryGap)
    (hStrong : DeclsStrong.{u} DeclOrigin) :
    IxVM.Consistency.L7.{u} (mkSeams DeclOrigin) := by
  intro _h1 _hDecls hClaim d value heap calls ev hbound bytes clm hde hpack hscope V seeds b hseeds hRT
  rcases hClaim d value heap calls ev hbound bytes clm hde hpack hscope V seeds b hseeds hRT with
    hcol | ⟨t, E₀, hadm, hload, hseedOk, hwalk⟩
  · exact Or.inl hcol
  · by_cases hcol : V.HashedCollision (bytes :: b.bytes :: IxVM.Consistency.committedImages) calls
    · exact Or.inl hcol
    · have hadmV : TableAdmittedComplete V b :=
        tableAdmittedComplete_of_tableAdmitted hBoundGap hRT.tableAdmitted hcol
      have hRole : ConsistentReadRole.{u} V calls b seeds :=
        consistentReadRole_of_rolePrelude_declsStrong
          rolePreludeInputs
          (safeRefsInputs hSafeGap)
          hStrong
          hbound hscope hseeds hRT hadmV hadm hload hseedOk hwalk
          (List.mem_cons_of_mem _ List.mem_cons_self)
          (fun img hm => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))
          hcol
      exact Or.inr (consistentRead_of_consistentReadRole hBoundGap hRole)

/-- **Circuit-level consistency (`IxVM.Consistency.CircuitConsistent`)** at `mkSeams DeclOrigin`
from `DeclsStrong DeclOrigin`, wiring `L0`–`L7` through `ClaimsL1L6.consistent_of_decls_l7`. -/
theorem consistent_mkSeams_of_declsStrong
    (hSafeGap : SafeExprRefsGap)
    (hBoundGap : StatementBoundaryGap)
    (hStrong : DeclsStrong.{u} DeclOrigin) :
    IxVM.Consistency.CircuitConsistent.{u} :=
  consistent_of_decls_l7 DeclOrigin hStrong.toDecls
    (l7_mkSeams_of_declsStrong hSafeGap hBoundGap hStrong)

end IxVM.Refinement.Assembly
