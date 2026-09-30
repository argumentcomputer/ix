/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Egress.Constant
import Ix.Kernel.Egress.Projection

/-! # Exact record round trips with retained Ixon layout

`readRecord` keeps the table/sharing choices that raw kernel syntax cannot
represent. `writeRecord` rebuilds declaration payloads from that raw syntax,
checks the output's complete reading, and reconstructs projection records
from kernel references. It never needs the original primary payload to write
it: replacing `Context.source` does not change the writer's result.

These are serialization readings, independent of declaration admission. A
round trip does not establish typing, byte canonicality, or address hashes.
-/

namespace Ix.Kernel.Egress

inductive Record where
  | primary (layout : ConstantLayout) (block : Block Address)
  | projection (layout : ProjectionLayout) (reference : ConstRef Address)

def Record.Reads (record : Record) (ctx : Ingress.Context) : Prop :=
  match record with
  | .primary _ block => Ingress.BlockReads ctx block
  | .projection layout reference => ProjectionReads ctx.source layout reference ∧
      Ingress.referenceSource ctx.constants ctx.owner ctx.source = some reference

def readRecordC (ctx : Ingress.Context) (fuel : Nat) :
    Search { record : Record // record.Reads ctx } := do
  if Ingress.isProjection ctx.source.info then
    let projection ← readProjectionC ctx.source
    if owner : Ingress.referenceSource ctx.constants ctx.owner ctx.source = some projection.val.2 then
      return ⟨.projection projection.val.1 projection.val.2, projection.property, owner⟩
    else throw (.malformed "projection does not resolve to its claimed owner and position")
  else
    let block ← Ingress.readBlockC ctx fuel
    return ⟨.primary (.ofConstant ctx.source) block.val, block.property⟩

def readRecord (ctx : Ingress.Context) (fuel : Nat) : Search Record :=
  (readRecordC ctx fuel).map Subtype.val

def writeRecord (ctx : Ingress.Context) (fuel : Nat) : Record → Search Ixon.Constant
  | .primary layout block => writeBlock ctx fuel layout block
  | .projection layout reference => do
    let source ← writeProjection layout reference
    if Ingress.referenceSource ctx.constants ctx.owner source = some reference then return source
    else .error (.malformed "projection does not resolve to its claimed owner and position")

theorem readRecord_reading {ctx : Ingress.Context} {fuel : Nat} {record : Record}
    (h : readRecord ctx fuel = .ok record) : record.Reads ctx := by
  obtain ⟨reading, _, same⟩ := Except.map_eq_ok h
  exact same ▸ reading.property

theorem writeRecord_reading {ctx : Ingress.Context} {fuel : Nat} {record : Record}
    {source : Ixon.Constant} (h : writeRecord ctx fuel record = .ok source) :
    record.Reads { ctx with source } := by
  cases record with
  | primary layout block => exact writeBlock_reading h
  | projection layout reference =>
    cases rebuilt : writeProjection layout reference with
    | error failure => simp [writeRecord, rebuilt, bind, Except.bind] at h
    | ok output =>
      by_cases owner : Ingress.referenceSource ctx.constants ctx.owner output = some reference
      · simp [writeRecord, rebuilt, owner, bind, pure, Except.bind, Except.pure] at h
        subst source
        exact ⟨writeProjection_reading rebuilt, owner⟩
      · simp [writeRecord, rebuilt, owner, bind, Except.bind] at h

/-- Only tables in the retained layout and the external reference/blob context
are used when writing; the original primary payload is not consulted. -/
theorem writeRecord_source (ctx : Ingress.Context) (source : Ixon.Constant) (fuel : Nat) (record : Record) :
    writeRecord { ctx with source } fuel record = writeRecord ctx fuel record := by
  cases record <;> rfl

theorem record_roundtrip {ctx : Ingress.Context} {fuel : Nat} {record : Record}
    (h : readRecord ctx fuel = .ok record) : writeRecord ctx fuel record = .ok ctx.source := by
  unfold readRecord readRecordC at h
  by_cases projection : Ingress.isProjection ctx.source.info = true
  · simp only [projection, ↓reduceIte] at h
    cases read : readProjectionC ctx.source with
    | error failure => simp [read, bind, Except.bind, Except.map] at h
    | ok value =>
      by_cases owner : Ingress.referenceSource ctx.constants ctx.owner ctx.source = some value.val.2
      · simp [read, owner, bind, pure, Except.bind, Except.pure, Except.map] at h
        subst record
        simp [writeRecord, writeProjection_of_reading value.property, owner,
          bind, pure, Except.bind, Except.pure]
      · simp [read, owner, bind, Except.bind, Except.map] at h
  · simp only [projection] at h
    cases read : Ingress.readBlockC ctx fuel with
    | error failure => simp [read, bind, Except.bind, Except.map] at h
    | ok value =>
      simp [read, bind, pure, Except.bind, Except.pure, Except.map] at h
      subst record
      exact writeBlock_roundtrip (by simp [Ingress.readBlock, read, Except.map])

/-- Read every physical record in order, including projections. The supplied
store is the reference context; it need not have the input list's order. -/
def readRecords (constants : Ingress.Constants) (blobs : Ingress.Blobs)
    (natFamily : Option (ConstRef Address)) (fuel : Nat) :
    Ingress.Constants → Search (List (Address × Record))
  | [] => .ok []
  | (address, source) :: inputs => do
    let record ← readRecord (Ingress.Context.ofStores constants blobs address source natFamily) fuel
    let records ← readRecords constants blobs natFamily fuel inputs
    return (address, record) :: records

/-- Reconstruct payloads and retain every address and position. A blank
`Context.source` makes the writer's independence from that field explicit. -/
def writeRecords (constants : Ingress.Constants) (blobs : Ingress.Blobs)
    (natFamily : Option (ConstRef Address)) (fuel : Nat) :
    List (Address × Record) → Search Ingress.Constants
  | [] => .ok []
  | (address, record) :: records => do
    let source ← writeRecord
      (Ingress.Context.ofStores constants blobs address ⟨.muts #[], #[], #[], #[]⟩ natFamily) fuel record
    let sources ← writeRecords constants blobs natFamily fuel records
    return (address, source) :: sources

def RecordsRead (constants : Ingress.Constants) (blobs : Ingress.Blobs)
    (natFamily : Option (ConstRef Address))
    (inputs : Ingress.Constants) (records : List (Address × Record)) : Prop :=
  Forall₂ (fun input record => record.1 = input.1 ∧
    record.2.Reads (Ingress.Context.ofStores constants blobs input.1 input.2 natFamily)) inputs records

theorem readRecords_reading {constants inputs : Ingress.Constants} {blobs : Ingress.Blobs}
    {natFamily : Option (ConstRef Address)} {fuel : Nat} {records : List (Address × Record)}
    (h : readRecords constants blobs natFamily fuel inputs = .ok records) :
    RecordsRead constants blobs natFamily inputs records := by
  induction inputs generalizing records with
  | nil =>
    simp only [readRecords, Except.ok.injEq] at h
    subst records
    exact .nil
  | cons input inputs ih =>
    obtain ⟨address, source⟩ := input
    cases head : readRecord (Ingress.Context.ofStores constants blobs address source natFamily) fuel with
    | error failure => simp [readRecords, head, bind, Except.bind] at h
    | ok record =>
      cases tail : readRecords constants blobs natFamily fuel inputs with
      | error failure => simp [readRecords, head, tail, bind, Except.bind] at h
      | ok rest =>
        simp [readRecords, head, tail, bind, pure, Except.bind, Except.pure] at h
        subst records
        exact .cons ⟨rfl, readRecord_reading head⟩ (ih tail)

theorem writeRecords_reading {constants inputs : Ingress.Constants} {blobs : Ingress.Blobs}
    {natFamily : Option (ConstRef Address)} {fuel : Nat} {records : List (Address × Record)}
    (h : writeRecords constants blobs natFamily fuel records = .ok inputs) :
    RecordsRead constants blobs natFamily inputs records := by
  induction records generalizing inputs with
  | nil =>
    simp only [writeRecords, Except.ok.injEq] at h
    subst inputs
    exact .nil
  | cons entry records ih =>
    obtain ⟨address, record⟩ := entry
    cases head : writeRecord
        (Ingress.Context.ofStores constants blobs address ⟨.muts #[], #[], #[], #[]⟩ natFamily) fuel record with
    | error failure => simp [writeRecords, head, bind, Except.bind] at h
    | ok source =>
      cases tail : writeRecords constants blobs natFamily fuel records with
      | error failure => simp [writeRecords, head, tail, bind, Except.bind] at h
      | ok rest =>
        simp [writeRecords, head, tail, bind, pure, Except.bind, Except.pure] at h
        subst inputs
        exact .cons ⟨rfl, writeRecord_reading head⟩ (ih tail)

/-- Exact list equality includes addresses, record order, projection variants,
all declaration fields, and all retained table/sharing choices. This is a
reading round trip, independent of typing, hashes, and byte canonicality. -/
theorem records_roundtrip {constants inputs : Ingress.Constants} {blobs : Ingress.Blobs}
    {natFamily : Option (ConstRef Address)} {fuel : Nat} {records : List (Address × Record)}
    (h : readRecords constants blobs natFamily fuel inputs = .ok records) :
    writeRecords constants blobs natFamily fuel records = .ok inputs := by
  induction inputs generalizing records with
  | nil =>
    simp only [readRecords, Except.ok.injEq] at h
    subst records
    rfl
  | cons input inputs ih =>
    obtain ⟨address, source⟩ := input
    cases head : readRecord (Ingress.Context.ofStores constants blobs address source natFamily) fuel with
    | error failure => simp [readRecords, head, bind, Except.bind] at h
    | ok record =>
      cases tail : readRecords constants blobs natFamily fuel inputs with
      | error failure => simp [readRecords, head, tail, bind, Except.bind] at h
      | ok rest =>
        simp [readRecords, head, tail, bind, pure, Except.bind, Except.pure] at h
        subst records
        have rebuilt := record_roundtrip head
        rw [← writeRecord_source _ ⟨.muts #[], #[], #[], #[]⟩] at rebuilt
        change writeRecord (Ingress.Context.ofStores constants blobs address
          ⟨.muts #[], #[], #[], #[]⟩ natFamily) fuel record = .ok source at rebuilt
        simp only [writeRecords, rebuilt, ih tail, bind, pure, Except.bind, Except.pure]

end Ix.Kernel.Egress
