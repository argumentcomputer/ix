import Ix.Cert.ReaderStreamsUnits

/-! # A closure order in quotient Source's order, segment by segment

`ReaderStreamsUnits.UnitsRead` asks for a closure order whose records read as quotient
Source's trace, unit by unit. This module builds that from the trace's order: the order is
a prefix of addresses with no stored record (a projection's block left out of the store),
then one segment per Source read, in the trace's order. A Source read that changes no entry
has a segment of records each read to nothing from every state; any other has a segment that
holds its partner record, read from every state related to the Source state as the Source
read renamed, among records read to nothing (`SegmentsRead`). Such segments read
as the trace's units (`units_of_segments`, `unitsRead_of_segments`), and the order respects
the records' references whenever a rank that every reference descends orders it
(`ordered_of_rank`). -/

namespace Ix.Cert.ClosureSegments

open Ix.Kernel
open Ix.Kernel.Reader (State Read Ctx readRecord)

variable {md md' : Mode}

/-- A record read to nothing from every state. -/
def InertAt (cx : Ctx md') (a : Address) (c : Ixon.Constant) : Prop :=
  ∀ stA : State md', ∃ rA, readRecord cx stA a c = .ok rA ∧ StreamRename.Inert rA

/-- Addresses whose records, where stored, read to nothing from every state. -/
def InertAddrs (ixe : Ixon.Env) (cx : Ctx md') (as : List Address) : Prop :=
  ∀ a ∈ as, ∀ c, recordAt ixe a = some c → InertAt cx a c

/-- **A Source read's segment of the closure order**: an inert Source read with records read
to nothing, or a Source read in the scope whose segment holds its partner record, read from
every related state as the Source read renamed, between records read to nothing. -/
def SegmentReads (f : md.Id → md'.Id) (P : KeyScope md) (cx : Ctx md') (ixe : Ixon.Env) (stS : State md)
    (rS : Read md) (seg : List Address) : Prop :=
  (StreamRename.Inert rS ∧ InertAddrs ixe cx seg) ∨
    ∃ before a after c, seg = before ++ a :: after ∧ recordAt ixe a = some c ∧
      StreamUnits.ReadScoped P rS ∧
      (∀ stA : State md', StreamRename.StateRen f P stS stA →
        ∃ rA, readRecord cx stA a c = .ok rA ∧ StreamUnits.ReadRen f rS rA) ∧
      InertAddrs ixe cx before ∧ InertAddrs ixe cx after

/-- **The segments of a trace**, one per Source read, each read from the Source state the
reads before it leave. -/
inductive SegmentsRead (f : md.Id → md'.Id) (P : KeyScope md) (cx : Ctx md') (ixe : Ixon.Env) :
    State md → List (Read md) → List (List Address) → Prop where
  | nil {stS : State md} : SegmentsRead f P cx ixe stS [] []
  | cons {stS : State md} {rS : Read md} {rs : List (Read md)} {seg : List Address} {segs : List (List Address)}
      (head : SegmentReads f P cx ixe stS rS seg) (tail : SegmentsRead f P cx ixe (stS.commit rS) rs segs) :
      SegmentsRead f P cx ixe stS (rS :: rs) (seg :: segs)

theorem decodedOf_append (ixe : Ixon.Env) (l₁ l₂ : List Address) :
    Stream.decodedOf ixe (l₁ ++ l₂) = Stream.decodedOf ixe l₁ ++ Stream.decodedOf ixe l₂ := by
  unfold Stream.decodedOf
  rw [List.filterMap_append]

/-- Records read to nothing from every state open any stream of units. -/
theorem units_inert {f : md.Id → md'.Id} {P : KeyScope md} {cx : Ctx md'} {ixe : Ixon.Env} {stS : State md}
    {rs : List (Read md)} {R : List (Address × Ixon.Constant)} (h : StreamUnits.Units f P cx stS rs R) :
    ∀ {as : List Address}, InertAddrs ixe cx as → StreamUnits.Units f P cx stS rs (Stream.decodedOf ixe as ++ R)
  | [], _ => h
  | a :: as, hi => by
    rw [Stream.decodedOf_cons]
    have tail := units_inert h (as := as) fun b hb => hi b (List.mem_cons_of_mem _ hb)
    cases hc : recordAt ixe a with
    | none => exact tail
    | some c =>
      refine .inertRecord (fun stA _ => hi a List.mem_cons_self c hc stA) tail

/-- **Segments read as the trace's units.** -/
theorem units_of_segments {f : md.Id → md'.Id} {P : KeyScope md} {cx : Ctx md'} {ixe : Ixon.Env}
    {stS : State md} {rs : List (Read md)} {segs : List (List Address)} (h : SegmentsRead f P cx ixe stS rs segs) :
    StreamUnits.Units f P cx stS rs (Stream.decodedOf ixe segs.flatten) := by
  induction h with
  | nil => exact .nil
  | cons head _ ih =>
    rw [List.flatten_cons, decodedOf_append]
    rcases head with ⟨inert, hseg⟩ | ⟨before, a, after, c, rfl, hc, hscope, reads, hbefore, hafter⟩
    · exact units_inert (.inertSource inert ih) hseg
    · rw [decodedOf_append, Stream.decodedOf_cons, hc, List.append_assoc]
      exact units_inert (.record hscope reads (units_inert ih hafter)) hbefore

/-- **A closure order in the trace's order**: a prefix of addresses with no stored record,
then the segments, read as the trace's units. -/
theorem unitsRead_of_segments {ixe : Ixon.Env} {sub : Ix.Environment} {t : RoleTable}
    {preA : Reader.Prelude .anon} {b : Ix.RoleEvidence.Bundle} {pre : Reader.Prelude .source}
    {rs : List (Read .source)} (lead : List Address) (segs : List (List Address))
    (order : ClosureOrder ixe (Seed ixe sub) (lead ++ segs.flatten))
    (canonical : Stream.StoredCanonical ixe (lead ++ segs.flatten))
    (absent : ∀ a ∈ lead, recordAt ixe a = none)
    (reads : SegmentsRead (Ix.LeanIngress.evAddr ixe b) (KeyScope.ofId (Ix.LeanIngress.QRepAt ixe (Ix.LeanIngress.roleAtMap t)))
      (closureContext ixe t preA (lead ++ segs.flatten)) ixe pre.state rs segs) :
    ReaderStreamsUnits.UnitsRead ixe sub t preA b pre rs := by
  refine ⟨lead ++ segs.flatten, order, canonical, ?_⟩
  have hlead : Stream.decodedOf ixe lead = [] := by
    unfold Stream.decodedOf
    exact List.filterMap_eq_nil_iff.mpr fun a ha => by simp [absent a ha]
  rw [decodedOf_append, hlead, List.nil_append]
  exact units_of_segments reads

/-- **An order that a rank orders respects the records' references**, when every reference
descends the rank. -/
theorem ordered_of_rank {ixe : Ixon.Env} (rank : Address → Nat) (descends : ∀ a b, RecordRef ixe a b → rank b < rank a) :
    ∀ {L : List Address}, L.Pairwise (fun a b => rank a ≤ rank b) → L.Pairwise fun a b => ¬ RecordRef ixe a b := by
  intro L h
  exact h.imp fun {a b} hab href => absurd (descends a b href) (Nat.not_lt.mpr hab)

/-! ## Records read to nothing -/

/-- **A projection record reads to nothing** where its block resolves it. -/
theorem projection_inert (cx : Ctx md') (a : Address) (c : Ixon.Constant)
    (hproj : (∃ p, c.info = .dPrj p) ∨ (∃ p, c.info = .iPrj p) ∨ (∃ p, c.info = .rPrj p) ∨ ∃ p, c.info = .cPrj p)
    (resolves : (Reader.resolveSource cx.store a c).isSome = true) : InertAt cx a c := by
  intro stA
  refine ⟨{}, ?_, ⟨⟨rfl, rfl, rfl⟩, rfl⟩⟩
  unfold readRecord
  have hn : (Reader.resolveSource cx.store a c).isNone = false := by
    cases h : Reader.resolveSource cx.store a c with
    | none => rw [h] at resolves; cases resolves
    | some _ => rfl
  rcases hproj with ⟨p, hp⟩ | ⟨p, hp⟩ | ⟨p, hp⟩ | ⟨p, hp⟩ <;> simp [hp, hn] <;> rfl

/--
info: 'Ix.Cert.ClosureSegments.unitsRead_of_segments' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms unitsRead_of_segments

end Ix.Cert.ClosureSegments
