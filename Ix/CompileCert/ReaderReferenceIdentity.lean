import Ix.CompileCert.ReaderPinNames
import Ix.CompileCert.ReaderSourceSpines
import Init.Data.String.Lemmas.Pattern.TakeDrop.String

/-! Recover anonymous reference identity for non-recursor targets from the
actual reader's pin, key and generated-name construction. No identity claim
is made for an arbitrary externally supplied name function. -/

namespace Ix.CompileCert.ReaderReferenceIdentity

open Ix Kernel.Reader
open _root_.Ix.Kernel (ConstRef)

def baseName (pins : ReaderPinNames.Names) (ref : ConstRef Address) : Kernel.Name :=
  pins.getD ref (keyName ref)

theorem key_root (ref : ConstRef Address) : rootComponent (keyName ref) = some "ix" := by
  cases ref <;> rfl

theorem base_injective (pins : ReaderPinNames.Names) (safe : ReaderPinNames.Safe pins)
    (unique : ReaderPinNames.Injective pins) (left right : ConstRef Address)
    (same : baseName pins left = baseName pins right) : left = right := by
  unfold baseName at same
  simp only [Std.HashMap.getD_eq_getD_getElem?] at same
  cases leftFound : pins[left]? with
  | none =>
    cases rightFound : pins[right]? with
    | none => exact keyName_injective (by simpa only [leftFound, rightFound, Option.getD_none] using same)
    | some name =>
      have equal : keyName left = name := by simpa only [leftFound, rightFound, Option.getD_none, Option.getD_some] using same
      have root : rootComponent name = some "ix" := by rw [← equal, key_root]
      exact False.elim ((safe right name rightFound).1 root)
  | some name =>
    cases rightFound : pins[right]? with
    | none =>
      have equal : name = keyName right := by simpa only [leftFound, rightFound, Option.getD_none, Option.getD_some] using same
      have root : rootComponent name = some "ix" := by rw [equal, key_root]
      exact False.elim ((safe left name leftFound).1 root)
    | some other =>
      have equal : name = other := by simpa only [leftFound, rightFound, Option.getD_some] using same
      subst other
      exact unique left right name leftFound rightFound

def Generated (index : RecIndex) : Prop :=
  ∀ (ref : ConstRef Address) (entry : RecEntry), index.recs[ref]? = some entry →
    derivedShape entry.name = true ∧ ∃ parent label, entry.name = .str parent label

theorem entryName_generated (pins : ReaderPinNames.Names) (block : Address)
    (motive count : Nat) (order : Array Nat) :
    derivedShape (ReaderIndexEntries.entryName pins block motive count order) = true ∧
      ∃ parent label, ReaderIndexEntries.entryName pins block motive count order = .str parent label := by
  unfold ReaderIndexEntries.entryName
  split
  · exact ⟨rfl, _, _, rfl⟩
  · refine ⟨?_, _, _, rfl⟩
    have starts : ("rec_" ++ toString (motive - count + 1)).startsWith "rec_" = true := by
      rw [String.startsWith_string_iff, String.toList_append]
      exact List.prefix_append _ _
    change (("rec_" ++ toString (motive - count + 1) == "rec") ||
      ("rec_" ++ toString (motive - count + 1)).startsWith "rec_" ||
      ("rec_" ++ toString (motive - count + 1) == "_model")) = true
    simp only [starts, Bool.or_true, Bool.true_or]

theorem buildIndex_generated (store : Store) (pins : ReaderPinNames.Names)
    (records : Array (Address × Ixon.Constant)) : Generated (buildIndex store pins records) := by
  intro ref entry found
  obtain ⟨owner, constant, position, recursor, carriers, firstIndex, blockConstant, members,
    firstSlot, first, _, _, _, _, _, _, _, _, _, _, named⟩ :=
    (ReaderIndexEntries.buildIndex_valid store pins records).1 ref entry found
  rw [named]
  exact entryName_generated pins entry.block entry.motive (ReaderIndex.inductives members).size
    (ReaderIndex.orderFor carriers entry.block (ReaderIndex.inductives members).size)

theorem base_ne_generated (pins : ReaderPinNames.Names) (safe : ReaderPinNames.Safe pins)
    (ref : ConstRef Address) (name : Kernel.Name) (derived : derivedShape name = true)
    (shape : ∃ parent label, name = .str parent label) : baseName pins ref ≠ name := by
  intro same
  unfold baseName at same
  rw [Std.HashMap.getD_eq_getD_getElem?] at same
  cases found : pins[ref]? with
  | none =>
    simp only [found, Option.getD_none] at same
    obtain ⟨parent, label, written⟩ := shape
    rw [written] at same
    cases ref <;> simp [keyName] at same
  | some pinned =>
    simp only [found, Option.getD_some] at same
    have allowed := (safe ref pinned found).2
    rw [same, derived] at allowed
    cases allowed

theorem nameOf_base (reader : Ctx) (ref : ConstRef Address) (unindexed : reader.index.recs[ref]? = none) :
    reader.nameOf ref = baseName reader.pins.names ref := by
  simp only [Ctx.nameOf, unindexed, KeyNames.get_eq, baseName, Std.HashMap.getD_eq_getD_getElem?]
  cases reader.pins.names[ref]? <;> rfl

/-- A non-recursor target's identity is unique even among recursor names:
validated pins and encoded keys cannot equal a generated recursor name. -/
theorem nameOf_identity (reader : Ctx) (safe : ReaderPinNames.Safe reader.pins.names)
    (unique : ReaderPinNames.Injective reader.pins.names) (generated : Generated reader.index)
    (ref target : ConstRef Address) (unindexed : reader.index.recs[target]? = none)
    (same : reader.nameOf ref = reader.nameOf target) : ref = target := by
  cases found : reader.index.recs[ref]? with
  | none =>
    apply base_injective reader.pins.names safe unique ref target
    rw [← nameOf_base reader ref found, ← nameOf_base reader target unindexed]
    exact same
  | some entry =>
    have facts := generated ref entry found
    apply False.elim (base_ne_generated reader.pins.names safe target entry.name facts.1 facts.2 ?_)
    rw [← nameOf_base reader target unindexed, ← same]
    simp only [Ctx.nameOf, found]

/-- A coherently stored inductive member cannot also be an indexed recursor.
This uses the actual scanned member's provenance and disjoint payload kinds. -/
theorem inductive_unindexed (store : Store) (pins : ReaderPinNames.Names)
    (records : Array (Address × Ixon.Constant)) (coherent : ReaderIndexEntries.Coherent store records)
    (owner : Address) (constant : Ixon.Constant) (members : Array Ixon.MutConst)
    (position : Nat) (ind : Ixon.Inductive) (stored : store owner = some constant)
    (kind : constant.info = .muts members) (member : members[position]? = some (.indc ind)) :
    (buildIndex store pins records).recs[ConstRef.member owner position]? = none := by
  cases found : (buildIndex store pins records).recs[ConstRef.member owner position]? with
  | none => rfl
  | some entry =>
    obtain ⟨actualOwner, actualConstant, actualPosition, recursor, carriers, reference, actualStored, actualMember, _⟩ :=
      ReaderIndexEntries.entry_stored store pins records coherent (.member owner position) entry found
    have refs := ConstRef.member.inj reference
    rcases refs with ⟨rfl, rfl⟩
    have constants : actualConstant = constant := Option.some.inj (actualStored.symm.trans stored)
    subst actualConstant
    have source := ReaderIndexEntries.member_source constant position recursor actualMember
    rw [kind] at source
    change members[position]? = some (.recr recursor) at source
    rw [member] at source
    cases Option.some.inj source

theorem inductiveAt_unindexed (store : Store) (pins : ReaderPinNames.Names)
    (records : Array (Address × Ixon.Constant)) (coherent : ReaderIndexEntries.Coherent store records)
    (ref : ConstRef Address) (ind : Ixon.Inductive) (available : inductiveAt store ref = some ind) :
    (buildIndex store pins records).recs[ref]? = none := by
  cases ref with
  | ctor owner position ctor => cases available
  | member owner position =>
    cases stored : store owner with
    | none => simp [inductiveAt, stored] at available
    | some constant =>
      cases kind : constant.info with
      | muts members =>
        cases member : members[position]? with
        | none => simp [inductiveAt, stored, kind, member] at available
        | some value =>
          cases value with
          | indc actual => exact inductive_unindexed store pins records coherent owner constant members position actual stored kind member
          | _ => simp [inductiveAt, stored, kind, member] at available
      | _ => simp [inductiveAt, stored, kind] at available

/-- The actual indexed context makes every stored inductive reference
identifiable from its internal logical name, without whole-name injectivity. -/
theorem inductive_identity (reader : Ctx) (records : Array (Address × Ixon.Constant))
    (built : reader.index = buildIndex reader.store reader.pins.names records)
    (coherent : ReaderIndexEntries.Coherent reader.store records)
    (safe : ReaderPinNames.Safe reader.pins.names) (unique : ReaderPinNames.Injective reader.pins.names)
    (ref target : ConstRef Address) (ind : Ixon.Inductive) (available : inductiveAt reader.store target = some ind)
    (same : reader.nameOf ref = reader.nameOf target) : ref = target := by
  apply nameOf_identity reader safe unique
    (by rw [built]; exact buildIndex_generated reader.store reader.pins.names records) ref target _ same
  rw [built]
  exact inductiveAt_unindexed reader.store reader.pins.names records coherent target ind available

/-- All identity conditions are derived for the real stream context from
checked pins, decoded compiler records and the committed prelude. -/
theorem stream_identity (environment : Ix.CompileM.CompileEnv) (limits : Kernel.Admission.Limits)
    (constants : Kernel.Ingress.Constants)
    (decoded : Kernel.Admission.decodeRecords limits environment.constants.toList = .ok constants)
    (pins : Pins) (pinsReady : defaultPins = .ok pins) (pre : Prelude) (preludeReady : builtinPrelude = .ok pre)
    (hint : ConstRef Address → Option Kernel.ReducibilityHint) (ref target : ConstRef Address) (ind : Ixon.Inductive)
    (available : inductiveAt (Kernel.Admission.streamContext pins pre constants environment.blobs.toList hint).store target = some ind)
    (same : (Kernel.Admission.streamContext pins pre constants environment.blobs.toList hint).nameOf ref =
      (Kernel.Admission.streamContext pins pre constants environment.blobs.toList hint).nameOf target) : ref = target := by
  have pinFacts := ReaderPinNames.defaultPins_valid pins pinsReady
  exact inductive_identity _ (ReaderStore.allRecords constants.toArray pre.records) rfl
    (ReaderAdmissionRecords.stream_coherent environment limits constants decoded pins pre preludeReady hint)
    pinFacts.1 pinFacts.2 ref target ind available same

/-- A functional source-to-logical-name association now gives exact anonymous
reference identity for an inductive role; aliases between source names remain
permitted. -/
theorem source_reference_exact (reader : Ctx) (records : Array (Address × Ixon.Constant))
    (built : reader.index = buildIndex reader.store reader.pins.names records)
    (coherent : ReaderIndexEntries.Coherent reader.store records)
    (safe : ReaderPinNames.Safe reader.pins.names) (unique : ReaderPinNames.Injective reader.pins.names)
    (names : Name → Kernel.Name → Prop) (source : Name) (target : ConstRef Address) (ind : Ixon.Inductive)
    (available : inductiveAt reader.store target = some ind)
    (identified : ∀ name, names source name → name = reader.nameOf target)
    (result : Option (ConstRef Address))
    (resolved : ∃ ref, result = some ref ∧ names source (reader.nameOf ref)) : result = some target := by
  obtain ⟨ref, found, mapped⟩ := resolved
  have same := inductive_identity reader records built coherent safe unique ref target ind available (identified _ mapped)
  simpa only [same] using found

theorem stream_source_reference_exact (environment : Ix.CompileM.CompileEnv) (limits : Kernel.Admission.Limits)
    (constants : Kernel.Ingress.Constants)
    (decoded : Kernel.Admission.decodeRecords limits environment.constants.toList = .ok constants)
    (pins : Pins) (pinsReady : defaultPins = .ok pins) (pre : Prelude) (preludeReady : builtinPrelude = .ok pre)
    (hint : ConstRef Address → Option Kernel.ReducibilityHint)
    (names : Name → Kernel.Name → Prop) (source : Name) (target : ConstRef Address) (ind : Ixon.Inductive)
    (available : inductiveAt (Kernel.Admission.streamContext pins pre constants environment.blobs.toList hint).store target = some ind)
    (identified : ∀ name, names source name →
      name = (Kernel.Admission.streamContext pins pre constants environment.blobs.toList hint).nameOf target)
    (result : Option (ConstRef Address))
    (resolved : ∃ ref, result = some ref ∧
      names source ((Kernel.Admission.streamContext pins pre constants environment.blobs.toList hint).nameOf ref)) :
    result = some target := by
  obtain ⟨ref, found, mapped⟩ := resolved
  have same := stream_identity environment limits constants decoded pins pinsReady pre preludeReady hint
    ref target ind available (identified _ mapped)
  simpa only [same] using found

/-- The earlier source-carrier theorem now returns the required exact member
reference, using properties of the constructed context rather than assuming
injectivity of `nameOf`. -/
theorem source_carrier_exact (reader : ECx) (empty : reader.src.sharing = #[]) (owner : Address)
    (self : ReaderSourceSpines.SelfAligned reader owner)
    (records : Array (Address × Ixon.Constant))
    (built : reader.cx.index = buildIndex reader.cx.store reader.cx.pins.names records)
    (coherent : ReaderIndexEntries.Coherent reader.cx.store records)
    (safe : ReaderPinNames.Safe reader.cx.pins.names) (unique : ReaderPinNames.Injective reader.cx.pins.names)
    (names : Name → Kernel.Name → Prop) (sourceParams : List Name) (params : List Kernel.Name)
    (source : Ix.Expr) (expression : Ixon.Expr)
    (meaning : ReaderSourceSpines.SourceRead reader names sourceParams params source expression)
    (count : Nat) (binderBound : count < spineFuel) (types : List Ix.Expr) (body : Ix.Expr)
    (parsed : ReaderSourceSpines.sourceStrip count source = some (types, body))
    (terminal : ReaderSourceSpines.SourceNonForall body) (domain : Ix.Expr) (last : types.getLast? = some domain)
    (enough : ReaderSourceSpines.sourceAppDepth domain < spineFuel)
    (name : Name) (levels : Array Level) (hash : Address)
    (head : ReaderSourceSpines.sourceHead domain = .const name levels hash)
    (target : ConstRef Address) (ind : Ixon.Inductive) (available : inductiveAt reader.cx.store target = some ind)
    (identified : ∀ value, names name value → value = reader.cx.nameOf target) :
    ReaderSpines.carrier reader.cx.store owner reader.src expression = some target :=
  source_reference_exact reader.cx records built coherent safe unique names name target ind available identified _
    (ReaderSourceSpines.source_carrier reader empty owner self names sourceParams params source expression meaning
      count binderBound types body parsed terminal domain last enough name levels hash head)

theorem source_lastHead_exact (reader : ECx) (empty : reader.src.sharing = #[]) (owner : Address)
    (self : ReaderSourceSpines.SelfAligned reader owner)
    (records : Array (Address × Ixon.Constant))
    (built : reader.cx.index = buildIndex reader.cx.store reader.cx.pins.names records)
    (coherent : ReaderIndexEntries.Coherent reader.cx.store records)
    (safe : ReaderPinNames.Safe reader.cx.pins.names) (unique : ReaderPinNames.Injective reader.cx.pins.names)
    (names : Name → Kernel.Name → Prop) (sourceParams : List Name) (params : List Kernel.Name)
    (types : List Ix.Expr) (rawTypes : List Ixon.Expr)
    (related : List.Forall₂ (ReaderSourceSpines.SourceRead reader names sourceParams params) types rawTypes)
    (source : Ix.Expr) (last : types.getLast? = some source)
    (enough : ReaderSourceSpines.sourceAppDepth source < spineFuel)
    (name : Name) (levels : Array Level) (hash : Address)
    (head : ReaderSourceSpines.sourceHead source = .const name levels hash)
    (target : ConstRef Address) (ind : Ixon.Inductive) (available : inductiveAt reader.cx.store target = some ind)
    (identified : ∀ value, names name value → value = reader.cx.nameOf target) :
    ReaderSpines.lastHead reader.cx.store owner reader.src rawTypes = some target :=
  source_reference_exact reader.cx records built coherent safe unique names name target ind available identified _
    (ReaderSourceSpines.source_lastHead reader empty owner self names sourceParams params types rawTypes related
      source last enough name levels hash head)

end Ix.CompileCert.ReaderReferenceIdentity
