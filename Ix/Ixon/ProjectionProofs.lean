/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Projection
import Ix.Ixon.Verify.Admission
import Ix.Ixon.ConLecheConsistency

namespace Ix.Ixon.Projection

open Kernel

/-- Projection identities are determined by the physical member kind and
array positions. Constructor metadata is checked later by kernel ingress. -/
inductive MemberRequest (owner : Address) (index : Nat) : _root_.Ixon.MutConst → Request → Prop where
  | definition : MemberRequest owner index (.defn value) ⟨.definition, .member owner index⟩
  | recursor : MemberRequest owner index (.recr value) ⟨.recursor, .member owner index⟩
  | family : MemberRequest owner index (.indc value) ⟨.inductive, .member owner index⟩
  | constructor (found : value.ctors[position]? = some ctor) :
      MemberRequest owner index (.indc value) ⟨.constructor, .ctor owner index position⟩

def Requested (constants : Ingress.Constants) (request : Request) : Prop :=
  ∃ owner source members member index, (owner, source) ∈ constants ∧ source.info = .muts members ∧
    members[index]? = some member ∧ MemberRequest owner index member request

theorem memberRequests_spec (owner : Address) (index : Nat) (member : _root_.Ixon.MutConst)
    (request : Request) : request ∈ memberRequests owner index member ↔
      MemberRequest owner index member request := by
  cases member with
  | defn value =>
    constructor
    · intro h
      have same : request = ⟨.definition, .member owner index⟩ := by simpa [memberRequests] using h
      subst request
      exact .definition
    · intro h
      cases h
      simp [memberRequests]
  | recr value =>
    constructor
    · intro h
      have same : request = ⟨.recursor, .member owner index⟩ := by simpa [memberRequests] using h
      subst request
      exact .recursor
    · intro h
      cases h
      simp [memberRequests]
  | indc value =>
    constructor
    · intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact .family
      · obtain ⟨⟨ctor, position⟩, found, rfl⟩ := List.mem_map.mp h
        exact .constructor (by simpa using List.mk_mem_zipIdx_iff_getElem?.mp found)
    · intro h
      cases h with
      | family => exact List.mem_cons_self
      | constructor found =>
        rename_i position ctor
        apply List.mem_cons_of_mem
        exact List.mem_map.mpr ⟨(ctor, position),
          List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using found), rfl⟩

theorem requests_spec (constants : Ingress.Constants) (request : Request) :
    request ∈ requests constants ↔ Requested constants request := by
  constructor
  · intro h
    obtain ⟨⟨owner, source⟩, sourceMem, h⟩ := List.mem_flatMap.mp h
    cases info : source.info with
    | muts members =>
      simp only [info] at h
      obtain ⟨⟨member, index⟩, found, requested⟩ := List.mem_flatMap.mp h
      exact ⟨owner, source, members, member, index, sourceMem, info,
        by simpa using List.mk_mem_zipIdx_iff_getElem?.mp found,
        (memberRequests_spec _ _ _ _).mp requested⟩
    | defn _ | recr _ | axio _ | quot _ | cPrj _ | rPrj _ | iPrj _ | dPrj _ => simp [info] at h
  · rintro ⟨owner, source, members, member, index, sourceMem, info, found, requested⟩
    apply List.mem_flatMap.mpr
    refine ⟨(owner, source), sourceMem, ?_⟩
    simp only [info]
    exact List.mem_flatMap.mpr ⟨(member, index),
      List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using found),
      (memberRequests_spec _ _ _ _).mpr requested⟩

/-- A structural projection reading together with its representable owner.
The writer checks positions fit UInt64 rather than silently wrapping them. -/
def Reads (request : Request) (record : _root_.Ixon.Constant) : Prop :=
  request.reference.block.hash.size = 32 ∧
    Egress.ProjectionReads record request.layout request.reference

/-- Each requested projection either reuses its exact existing payload or
adds the correctly addressed record at a fresh key. No input is overwritten. -/
inductive Added : List Request → Ingress.Constants → Ingress.Constants → Prop where
  | nil : Added [] constants constants
  | reuse (reading : Reads request record)
      (present : Ingress.lookup constants (address record) = some record)
      (tail : Added rest constants output) : Added (request :: rest) constants output
  | fresh (reading : Reads request record)
      (absent : Ingress.lookup constants (address record) = none)
      (tail : Added rest ((address record, record) :: constants) output) :
      Added (request :: rest) constants output

def Expanded (maxProjections : Nat) (input output : Ingress.Constants) : Prop :=
  (requests input).length ≤ maxProjections ∧ Added (requests input) input output

theorem address_width (record : _root_.Ixon.Constant) : (address record).hash.size = 32 :=
  (Blake3.Pure.hash (_root_.Ixon.serConstant record)).property

theorem Reads.projection {request : Request} {record : _root_.Ixon.Constant}
    (h : Reads request record) : Ingress.isProjection record.info = true := by
  rcases request with ⟨layout, reference⟩
  rcases h with ⟨_, reading⟩
  cases reading <;> rfl

theorem Reads.wireWF {request : Request} {record : _root_.Ixon.Constant}
    (h : Reads request record) : record.wireWF := by
  rcases request with ⟨layout, reference⟩
  rcases h with ⟨width, reading⟩
  cases reading <;> simpa [
    _root_.Ixon.Constant.wireWF, _root_.Ixon.ConstantInfo.wireWF,
    ConstRef.block] using width

theorem Reads.matchesRecord {request : Request} {record : _root_.Ixon.Constant}
    (h : Reads request record) : matchesRecord request record = true := by
  rcases request with ⟨layout, reference⟩
  rcases h with ⟨_, reading⟩
  cases reading <;> simp [Ix.Ixon.Projection.matchesRecord, Egress.readProjection,
    Egress.readProjectionC, Ingress.emptyTables, Except.map]

theorem matchesRecord_eq {request : Request} {existing record : _root_.Ixon.Constant}
    (h : matchesRecord request existing = true) (reading : Reads request record) : existing = record := by
  unfold matchesRecord at h
  cases parsed : Egress.readProjection existing with
  | error reason => simp [parsed] at h
  | ok result =>
    rcases result with ⟨layout, reference⟩
    simp only [parsed, decide_eq_true_eq] at h
    rcases h with ⟨rfl, rfl⟩
    have first := Egress.writeProjection_roundtrip parsed
    have second := Egress.writeProjection_of_reading reading.2
    rw [first] at second
    exact Except.ok.inj second

theorem reconstructLoop_spec {limit : Nat} {todo : List Request}
    {input output : Ingress.Constants} (h : reconstructLoop limit todo input = .ok output) :
    todo.length ≤ limit ∧ Added todo input output := by
  induction todo generalizing limit input with
  | nil =>
    simp only [reconstructLoop, Except.ok.injEq] at h
    subst output
    exact ⟨Nat.zero_le _, .nil⟩
  | cons request rest ih =>
    cases limit with
    | zero => cases h
    | succ limit =>
      unfold reconstructLoop at h
      split at h
      next bad => cases h
      next good =>
        have width : request.reference.block.hash.size = 32 := by simpa using good
        cases written : Egress.writeProjection request.layout request.reference with
        | error reason => simp [written, Except.mapError, bind, Except.bind] at h
        | ok record =>
          simp only [written, Except.mapError, bind, Except.bind] at h
          have reading : Reads request record := ⟨width, Egress.writeProjection_reading written⟩
          cases found : Ingress.lookup input (address record) with
          | none =>
            simp only [found] at h
            obtain ⟨count, tail⟩ := ih h
            exact ⟨by simpa using Nat.succ_le_succ count, .fresh reading found tail⟩
          | some existing =>
            simp only [found] at h
            split at h
            next same =>
              have same := matchesRecord_eq same reading
              subst existing
              obtain ⟨count, tail⟩ := ih h
              exact ⟨by simpa using Nat.succ_le_succ count, .reuse reading found tail⟩
            next => cases h

theorem reconstruct_spec {limit : Nat} {input output : Ingress.Constants}
    (h : reconstruct limit input = .ok output) : Expanded limit input output :=
  reconstructLoop_spec h

theorem reconstructLoop_complete {todo : List Request} {input output : Ingress.Constants}
    (h : Added todo input output) {limit : Nat} (fits : todo.length ≤ limit) :
    reconstructLoop limit todo input = .ok output := by
  induction h generalizing limit with
  | nil => simp [reconstructLoop]
  | @reuse request record input rest output reading present tail ih =>
    cases limit with
    | zero => simp at fits
    | succ limit =>
      have remaining : rest.length ≤ limit := by simpa using fits
      simp [reconstructLoop, reading.1, -ConstRef.block, Egress.writeProjection_of_reading reading.2,
        present, reading.matchesRecord, ih remaining, bind, Except.bind, Except.mapError]
  | @fresh request record input rest output reading absent tail ih =>
    cases limit with
    | zero => simp at fits
    | succ limit =>
      have remaining : rest.length ≤ limit := by simpa using fits
      simp [reconstructLoop, reading.1, -ConstRef.block, Egress.writeProjection_of_reading reading.2,
        absent, ih remaining, bind, Except.bind, Except.mapError]

theorem reconstruct_ok_iff (limit : Nat) (input output : Ingress.Constants) :
    reconstruct limit input = .ok output ↔ Expanded limit input output :=
  ⟨reconstruct_spec, fun h => reconstructLoop_complete h.2 h.1⟩

theorem Added.preserves {todo : List Request} {input output : Ingress.Constants}
    (h : Added todo input output) {pair : Address × _root_.Ixon.Constant} (mem : pair ∈ input) :
    pair ∈ output := by
  induction h with
  | nil => exact mem
  | reuse _ _ _ ih => exact ih mem
  | fresh _ _ _ ih => exact ih (List.mem_cons_of_mem _ mem)

theorem Added.lookup {todo : List Request} {input output : Ingress.Constants}
    (h : Added todo input output) {key : Address} {record : _root_.Ixon.Constant}
    (found : Ingress.lookup input key = some record) : Ingress.lookup output key = some record := by
  induction h with
  | nil => exact found
  | reuse _ _ _ ih => exact ih found
  | @fresh request added input rest output reading absent tail ih =>
    apply ih
    have different : address added ≠ key := by
      intro same
      rw [same, found] at absent
      cases absent
    simpa [Ingress.lookup, different] using found

/-- Every requested projection is present under its computed address after
successful reconstruction, including requests that reused supplied records. -/
theorem Added.complete {todo : List Request} {input output : Ingress.Constants}
    (h : Added todo input output) {request : Request} (mem : request ∈ todo) :
    ∃ record, Reads request record ∧ Ingress.lookup output (address record) = some record := by
  induction h with
  | nil => cases mem
  | reuse reading present tail ih =>
    rcases List.mem_cons.mp mem with rfl | mem
    · exact ⟨_, reading, tail.lookup present⟩
    · exact ih mem
  | fresh reading absent tail ih =>
    rcases List.mem_cons.mp mem with rfl | mem
    · exact ⟨_, reading, tail.lookup (by simp [Ingress.lookup])⟩
    · exact ih mem

theorem Added.primaries {todo : List Request} {input output : Ingress.Constants}
    (h : Added todo input output) : primaries output = primaries input := by
  induction h with
  | nil => rfl
  | reuse _ _ _ ih => exact ih
  | fresh reading _ _ ih => simpa [Projection.primaries, reading.projection] using ih

theorem Added.length {todo : List Request} {input output : Ingress.Constants}
    (h : Added todo input output) : output.length ≤ input.length + todo.length := by
  induction h with
  | nil => simp
  | reuse _ _ _ ih => simp only [List.length_cons]; omega
  | fresh _ _ _ ih => simp only [List.length_cons] at *; omega

theorem Expanded.length {limit : Nat} {input output : Ingress.Constants}
    (h : Expanded limit input output) : output.length ≤ input.length + limit := by
  have := h.2.length
  have := h.1
  omega

theorem Expanded.complete {limit : Nat} {input output : Ingress.Constants}
    (h : Expanded limit input output) {request : Request} (requested : Requested input request) :
    ∃ record, Reads request record ∧ Ingress.lookup output (address record) = some record :=
  h.2.complete ((requests_spec _ _).mpr requested)

theorem Added.origin {todo : List Request} {input output : Ingress.Constants}
    (h : Added todo input output) {pair : Address × _root_.Ixon.Constant} (mem : pair ∈ output) :
    pair ∈ input ∨ ∃ request ∈ todo, Reads request pair.2 ∧ pair.1 = address pair.2 := by
  induction h with
  | nil => exact .inl mem
  | reuse _ _ _ ih =>
    rcases ih mem with old | ⟨request, requested, reading, hashed⟩
    · exact .inl old
    · exact .inr ⟨request, List.mem_cons_of_mem _ requested, reading, hashed⟩
  | fresh reading _ _ ih =>
    rcases ih mem with old | ⟨request, requested, reading, hashed⟩
    · rcases List.mem_cons.mp old with rfl | old
      · exact .inr ⟨_, List.mem_cons_self, reading, rfl⟩
      · exact .inl old
    · exact .inr ⟨request, List.mem_cons_of_mem _ requested, reading, hashed⟩

theorem Expanded.origin {limit : Nat} {input output : Ingress.Constants}
    (h : Expanded limit input output) {pair : Address × _root_.Ixon.Constant} (mem : pair ∈ output) :
    pair ∈ input ∨ ∃ request, Requested input request ∧ Reads request pair.2 ∧
      pair.1 = Address.blake3Pure (_root_.Ixon.serConstant pair.2) := by
  rcases h.2.origin mem with old | ⟨request, requested, reading, hashed⟩
  · exact .inl old
  · exact .inr ⟨request, (requests_spec _ _).mp requested, reading, hashed⟩

theorem Reads.decode {request : Request} {record : _root_.Ixon.Constant}
    (h : Reads request record) :
    _root_.Ixon.deConstantExact (_root_.Ixon.serConstant record) = .ok record :=
  Verify.deConstantExact_serConstant record h.wireWF

universe v

/-! ## The certified entry (L5) -/

open Ix.Kernel.ConLecheReader (defaultPins builtinPrelude builtinNatOpPins)

theorem checkBytes_run_iff (maxProjections : Nat) (limits : Admission.Limits)
    (records : Admission.Records) (blobs : Ingress.Blobs)
    (hint : ConstRef Address → Option ConLeche.ReducibilityHint) (env : ConLeche.Env) :
    checkBytes maxProjections limits records blobs hint = .ok env ↔
      Admission.preflight limits records blobs = .ok () ∧
      Admission.uniqueKeys records blobs = .ok () ∧ ∃ input output,
        Admission.decodeRecords limits records = .ok input ∧
        reconstruct maxProjections input = .ok output ∧
        ConLecheAdmission.checkConstants output blobs hint = .ok env := by
  cases flight : Admission.preflight limits records blobs with
  | error reason => simp [checkBytes, flight, Except.mapError, bind, Except.bind]
  | ok value =>
    cases value
    cases unique : Admission.uniqueKeys records blobs with
    | error reason => simp [checkBytes, flight, unique, Except.mapError, bind, Except.bind]
    | ok value =>
      cases value
      cases decoded : Admission.decodeRecords limits records with
      | error reason => simp [checkBytes, flight, unique, decoded, Except.mapError, bind, Except.bind]
      | ok input =>
        cases expanded : reconstruct maxProjections input with
        | error reason =>
          simp [checkBytes, flight, unique, decoded, expanded, Except.mapError, bind, Except.bind]
        | ok output =>
          cases checked : ConLecheAdmission.checkConstants output blobs hint <;>
            simp [checkBytes, flight, unique, decoded, expanded, checked, Except.mapError, bind,
              Except.bind]

/-- Exact byte reading, bounded projection extension, and the certified
checker on the expanded records. -/
theorem checkBytes_ok_iff (maxProjections : Nat) (limits : Admission.Limits)
    (records : Admission.Records) (blobs : Ingress.Blobs)
    (hint : ConstRef Address → Option ConLeche.ReducibilityHint) (env : ConLeche.Env) :
    checkBytes maxProjections limits records blobs hint = .ok env ↔
      Verify.Admission.WithinBatch limits records blobs ∧
      Verify.Admission.UniqueKeys records blobs ∧ ∃ input output,
        Verify.Admission.RecordsRead limits records input ∧ Expanded maxProjections input output ∧
        ConLecheAdmission.checkConstants output blobs hint = .ok env := by
  simp only [checkBytes_run_iff, Verify.Admission.preflight_ok_iff, Verify.Admission.uniqueKeys_ok_iff,
    Verify.Admission.decodeRecords_ok_iff, reconstruct_ok_iff]

/-- Every checker outcome is preserved after a bounded canonical reading and
projection extension. -/
theorem checkBytes_of_expansion {maxProjections : Nat} {limits : Admission.Limits}
    {records : Admission.Records} {input output : Ingress.Constants} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint}
    (within : Verify.Admission.WithinBatch limits records blobs)
    (keys : Verify.Admission.UniqueKeys records blobs)
    (reading : Verify.Admission.RecordsRead limits records input)
    (expanded : Expanded maxProjections input output) :
    checkBytes maxProjections limits records blobs hint =
      (ConLecheAdmission.checkConstants output blobs hint).mapError .checker := by
  have flight := (Verify.Admission.preflight_ok_iff _ _ _).mpr within
  have unique := (Verify.Admission.uniqueKeys_ok_iff _ _).mpr keys
  have decoded := (Verify.Admission.decodeRecords_ok_iff _ _ _).mpr reading
  have reconstructed := (reconstruct_ok_iff _ _ _).mpr expanded
  simp [checkBytes, flight, unique, decoded, reconstructed, Except.mapError, bind, Except.bind]

/-- **Fidelity**: the supplied records and blobs use each address once, the
records read exactly, their projection extension is the computed one, and
the checker installed what the expanded records describe. -/
theorem checkBytes_reading {maxProjections : Nat} {limits : Admission.Limits}
    {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytes maxProjections limits records blobs hint = .ok env) :
    Verify.Admission.UniqueKeys records blobs ∧
    ∃ input output, Verify.Admission.RecordsRead limits records input ∧
      Expanded maxProjections input output ∧ ∃ pins pre natPins, defaultPins = .ok pins ∧
        builtinPrelude = .ok pre ∧ builtinNatOpPins = .ok natPins ∧
        ConLecheAdmission.Installed pins pre natPins output blobs hint env := by
  obtain ⟨_, keys, input, output, reading, expanded, checked⟩ := (checkBytes_ok_iff _ _ _ _ _ _).mp h
  obtain ⟨pins, pre, natPins, hp, hq, hn, hw⟩ := ConLecheAdmission.checkConstants_with checked
  exact ⟨keys, input, output, reading, expanded, pins, pre, natPins, hp, hq, hn,
    ConLecheAdmission.checkConstantsWith_installed hw⟩

/-- **Model existence** for the certified projection-omitting entry. -/
theorem checkBytes_has_model (V : Type v) [ConLeche.SetTheory V] {maxProjections : Nat}
    {limits : Admission.Limits} {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytes maxProjections limits records blobs hint = .ok env) :
    Nonempty (ConLeche.Model V env) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, installed⟩ := checkBytes_reading h
  exact installed.has_model V

/-- **No proof of `False`** for the certified projection-omitting entry. -/
theorem checkBytes_no_proof_of_False (V : Type v) [ConLeche.SetTheory V] {maxProjections : Nat}
    {limits : Admission.Limits} {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytes maxProjections limits records blobs hint = .ok env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const ConLeche.falseName [] → False := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, installed⟩ := checkBytes_reading h
  exact installed.no_proof_of_False V

end Ix.Ixon.Projection
