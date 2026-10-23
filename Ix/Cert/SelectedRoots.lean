import Ix.Cert.Closure
import Ix.Cert.Unchanged
import Ix.Compile.Pass.Clique.Row

/-! # The exact Source-cone reference selector for CQ5.4

This pure, unwired reference enumerator retains every direct cause, downstream
Source root and published clique row. It computes a Source closure per candidate;
it is not a scalable runtime algorithm. A reverse-index implementation must be
proved equivalent before compiler wiring. No admission or semantic theorem is
asserted here, and enumerating published rows does not prove required rows exist.
-/

namespace Ix.Cert.SelectedRoots

open Ix (Name)
open Ix.Compile.ChangedSet (ChangedSet Cause)

def logicalInput (env : Ix.Environment) : Ix.Environment := { consts := env.consts }

def AffectedName (env : Ix.Environment) (cs : ChangedSet) (n : Name) : Prop :=
  ∃ m, Reaches (logicalInput env) [n] m ∧ cs.contains m = true

/-- A missing final dependency still counts. `closure.consts` alone loses it. -/
def affected (env : Ix.Environment) (cs : ChangedSet) (n : Name) : Bool :=
  let E := logicalInput env
  let seen := closureLoop E (∅, [n])
  cs.contains n || E.consts.toList.any fun (a, ci) =>
    seen.contains a && (dependencies (recursorsByBlock E) ci).toList.any cs.contains

theorem affected_iff (env : Ix.Environment) (cs : ChangedSet) (n : Name) :
    affected env cs n = true ↔ AffectedName env cs n := by
  let E := logicalInput env
  have inv := Closure.closureLoop_inv (env := E) (roots := [n])
    (∅, [n]) (Closure.inv_init E [n])
  unfold affected AffectedName
  rw [Bool.or_eq_true, List.any_eq_true]
  constructor
  · rintro (hn | ⟨⟨a, ci⟩, ha, h⟩)
    · exact ⟨n, .root (by simp), hn⟩
    · simp only [Bool.and_eq_true] at h
      obtain ⟨marked, needed⟩ := h
      obtain ⟨d, hd, changed⟩ := List.any_eq_true.mp needed
      exact ⟨d, .step (inv.sound a marked)
        (Closure.dependencies_sound (Closure.get?_of_mem_toList ha) (Array.mem_toList_iff.mp hd)), changed⟩
  · rintro ⟨m, reached, changed⟩
    cases reached with
    | root hm =>
      have same : (m == n) = true := by simpa using hm
      exact .inl (by
        unfold ChangedSet.contains at changed ⊢
        rw [← Std.HashSet.contains_congr same]; exact changed)
    | @step a m reached edge =>
      obtain ⟨ci, stored, deps⟩ := edge
      have marked := Closure.marked_of_reaches inv reached (by
        rw [Std.HashMap.contains_eq_isSome_getElem?]
        exact Option.isSome_iff_exists.mpr ⟨ci, stored⟩)
      obtain ⟨k, same, hk⟩ := Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList.mp stored
      obtain ⟨d, hd, sameD⟩ := Closure.dependencies_complete stored ⟨ci, stored, deps⟩
      refine .inr ⟨(k, ci), hk, ?_⟩
      simp only [Bool.and_eq_true]
      constructor
      · rw [← Std.HashSet.contains_congr same]; exact marked
      · apply List.any_eq_true.mpr
        refine ⟨d, Array.mem_toList_iff.mpr hd, ?_⟩
        unfold ChangedSet.contains at changed ⊢
        rw [← Std.HashSet.contains_congr sameD]; exact changed

theorem affected_congr {env : Ix.Environment} {cs : ChangedSet} {n n' : Name}
    (same : (n == n') = true) : affected env cs n = affected env cs n' := by
  have transfer : ∀ {x y : Name}, (x == y) = true →
      ∀ {m}, Reaches (logicalInput env) [x] m → Reaches (logicalInput env) [y] m := by
    intro x y h m reached
    induction reached with
    | @root m hm =>
      have hmx : (m == x) = true := by simpa using hm
      exact .root (by simpa using BEq.trans hmx h)
    | step _ edge ih => exact .step ih edge
  apply Bool.eq_iff_iff.mpr
  rw [affected_iff, affected_iff]
  constructor
  · rintro ⟨m, hm, changed⟩; exact ⟨m, transfer same hm, changed⟩
  · rintro ⟨m, hm, changed⟩; exact ⟨m, transfer (BEq.symm same) hm, changed⟩

def PublishedIn (sub : Ix.Environment) (ixe : Ixon.Env) (n : Name) (a : Address) : Prop :=
  ∃ ci named, sub.consts.get? n = some ci ∧
    ixe.named.get? n = some named ∧ named.addr = a

def RequiredRoot (env : Ix.Environment) (cs : ChangedSet) (sub : Ix.Environment)
    (ixe : Ixon.Env) (a : Address) : Prop :=
  ∃ n, PublishedIn sub ixe n a ∧ AffectedName env cs n

inductive Reason where
  | direct (cause : Cause)
  | cascade
  | row
  deriving DecidableEq, BEq, Repr

structure Root where
  source : Name
  address : Address
  reason : Reason

def ClassifiedRoot (env : Ix.Environment) (cs : ChangedSet) (sub : Ix.Environment)
    (ixe : Ixon.Env) (r : Root) : Prop :=
  match r.reason with
  | .direct cause => ∃ e ∈ cs.entries, e.cause = cause ∧ e.name = r.source ∧
      PublishedIn sub ixe r.source r.address
  | .cascade => PublishedIn sub ixe r.source r.address ∧
      AffectedName env cs r.source ∧ cs.contains r.source = false
  | .row => ∃ e ∈ cs.entries, e.cause = .clique ∧ e.name = r.source ∧
      ∃ ci named, sub.consts.get? r.source = some ci ∧
        ixe.named.get? (Ix.Compile.Pass.Clique.rowName r.source) = some named ∧
        named.addr = r.address

def published? (sub : Ix.Environment) (ixe : Ixon.Env) (n : Name) : Option Address := do
  let _ ← sub.consts.get? n
  let named ← ixe.named.get? n
  pure named.addr

theorem published?_iff : published? sub ixe n = some a ↔ PublishedIn sub ixe n a := by
  simp [published?, PublishedIn, Option.bind_eq_some_iff]

theorem published_congr {n n' : Name} (same : (n == n') = true) :
    PublishedIn sub ixe n a ↔ PublishedIn sub ixe n' a := by
  simp only [PublishedIn, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr same]

def rowPublished? (sub : Ix.Environment) (ixe : Ixon.Env) (n : Name) : Option Address := do
  let _ ← sub.consts.get? n
  let named ← ixe.named.get? (Ix.Compile.Pass.Clique.rowName n)
  pure named.addr

theorem rowPublished?_iff : rowPublished? sub ixe n = some a ↔
    ∃ ci named, sub.consts.get? n = some ci ∧
      ixe.named.get? (Ix.Compile.Pass.Clique.rowName n) = some named ∧ named.addr = a := by
  simp [rowPublished?, Option.bind_eq_some_iff]

/-- Retain all causes, even when several entries publish the same address. -/
def directRoots (cs : ChangedSet) (sub : Ix.Environment) (ixe : Ixon.Env) : List Root :=
  cs.entries.toList.filterMap fun e =>
    (published? sub ixe e.name).map fun a => ⟨e.name, a, .direct e.cause⟩

def cascadeRoots (env : Ix.Environment) (cs : ChangedSet) (sub : Ix.Environment)
    (ixe : Ixon.Env) : List Root :=
  sub.consts.toList.filterMap fun (n, _) =>
    if cs.contains n = false ∧ affected env cs n = true then
      (published? sub ixe n).map fun a => ⟨n, a, .cascade⟩
    else none

/-- Observed rows only: required transported-WF row existence is a later proof. -/
def rowRoots (cs : ChangedSet) (sub : Ix.Environment) (ixe : Ixon.Env) : List Root :=
  cs.entries.toList.filterMap fun e =>
    if e.cause = .clique then
      (rowPublished? sub ixe e.name).map fun a => ⟨e.name, a, .row⟩
    else none

def select (env : Ix.Environment) (cs : ChangedSet) (sub : Ix.Environment)
    (ixe : Ixon.Env) : List Root :=
  directRoots cs sub ixe ++ cascadeRoots env cs sub ixe ++ rowRoots cs sub ixe

theorem select_sound {env cs sub ixe r} (h : r ∈ select env cs sub ixe) :
    ClassifiedRoot env cs sub ixe r := by
  simp only [select, List.mem_append] at h
  rcases h with (h | h) | h
  · obtain ⟨e, he, out⟩ := List.mem_filterMap.mp h
    obtain ⟨a, published, rfl⟩ := Option.map_eq_some_iff.mp out
    exact ⟨e, Array.mem_toList_iff.mp he, rfl, rfl, published?_iff.mp published⟩
  · obtain ⟨⟨n, ci⟩, _, out⟩ := List.mem_filterMap.mp h
    dsimp only at out
    split at out
    · rename_i chosen
      obtain ⟨a, published, rfl⟩ := Option.map_eq_some_iff.mp out
      exact ⟨published?_iff.mp published, (affected_iff ..).mp chosen.2, chosen.1⟩
    · cases out
  · obtain ⟨e, he, out⟩ := List.mem_filterMap.mp h
    split at out
    · rename_i clique
      obtain ⟨a, published, rfl⟩ := Option.map_eq_some_iff.mp out
      exact ⟨e, Array.mem_toList_iff.mp he, clique, rfl, rowPublished?_iff.mp published⟩
    · cases out

theorem select_complete {env cs sub ixe a reason}
    (h : ∃ n, ClassifiedRoot env cs sub ixe ⟨n, a, reason⟩) :
    ∃ r ∈ select env cs sub ixe, r.address = a ∧ r.reason = reason := by
  obtain ⟨n, h⟩ := h
  cases reason with
  | direct cause =>
    obtain ⟨e, he, hc, hn, pub⟩ := h
    refine ⟨⟨n, a, .direct cause⟩, ?_, rfl, rfl⟩
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_filterMap.mpr
    refine ⟨e, Array.mem_toList_iff.mpr he, ?_⟩
    simp only [hn, hc, published?_iff.mpr pub, Option.map_some]
  | cascade =>
    obtain ⟨pub, affectedN, unchanged⟩ := h
    obtain ⟨ci, named, stored, namedAt, addressAt⟩ := pub
    obtain ⟨k, same, hk⟩ := Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList.mp stored
    have pubK := (published_congr same).mp ⟨ci, named, stored, namedAt, addressAt⟩
    have changedK : cs.contains k = false := by
      unfold ChangedSet.contains at unchanged ⊢
      rw [← Std.HashSet.contains_congr same]; exact unchanged
    have affectedK : affected env cs k = true := by
      rw [← affected_congr same]; exact (affected_iff ..).mpr affectedN
    refine ⟨⟨k, a, .cascade⟩, ?_, rfl, rfl⟩
    apply List.mem_append_left
    apply List.mem_append_right
    apply List.mem_filterMap.mpr
    refine ⟨(k, ci), hk, ?_⟩
    simp [changedK, affectedK, published?_iff.mpr pubK]
  | row =>
    obtain ⟨e, he, hc, hn, pub⟩ := h
    refine ⟨⟨n, a, .row⟩, List.mem_append_right _ ?_, rfl, rfl⟩
    apply List.mem_filterMap.mpr
    refine ⟨e, Array.mem_toList_iff.mpr he, ?_⟩
    simp [hc, hn, rowPublished?_iff.mpr pub]

private theorem names_fold_iff (n : Name) (es : List Ix.Compile.ChangedSet.Entry)
    (seen : Std.HashSet Name) :
    (es.foldl (fun s e => s.insert e.name) seen).contains n = true ↔
      (∃ e ∈ es, (e.name == n) = true) ∨ seen.contains n = true := by
  induction es generalizing seen with
  | nil => simp
  | cons e es ih =>
    rw [List.foldl_cons, ih, Std.HashSet.contains_insert]
    simp only [Bool.or_eq_true, List.mem_cons]
    constructor
    · rintro (⟨p, hp, same⟩ | same | old)
      · exact .inl ⟨p, .inr hp, same⟩
      · exact .inl ⟨e, .inl rfl, same⟩
      · exact .inr old
    · rintro (⟨p, hp, same⟩ | old)
      · rcases hp with rfl | hp
        · exact .inr (.inl same)
        · exact .inl ⟨p, hp, same⟩
      · exact .inr (.inr old)

/-- Derived for the actual classifier, not an assumed final coverage premise. -/
theorem contains_iff_entry (env : Ix.Environment) (condensed : Ix.CondensedBlocks)
    (table : Ix.AuxGen.AuxTable) (ixe : Ixon.Env) (n : Name) :
    let cs := Ix.Compile.ChangedSet.ofCompile (logicalInput env) condensed table ixe
    cs.contains n = true ↔ ∃ e ∈ cs.entries, (e.name == n) = true := by
  dsimp only
  rw [Unchanged.ofCompile_eq]
  unfold ChangedSet.contains
  dsimp only
  rw [← Array.foldl_toList, names_fold_iff]
  simp

theorem required_covered_ofCompile {env condensed table sub ixe a}
    (h : RequiredRoot env
      (Ix.Compile.ChangedSet.ofCompile (logicalInput env) condensed table ixe) sub ixe a) :
    ∃ r ∈ select env
      (Ix.Compile.ChangedSet.ofCompile (logicalInput env) condensed table ixe) sub ixe,
      r.address = a := by
  let cs := Ix.Compile.ChangedSet.ofCompile (logicalInput env) condensed table ixe
  obtain ⟨n, pub, affectedN⟩ := h
  have classified : ∃ reason n, ClassifiedRoot env cs sub ixe ⟨n, a, reason⟩ := by
    cases hc : cs.contains n with
    | false => exact ⟨.cascade, n, pub, affectedN, hc⟩
    | true =>
      obtain ⟨e, he, same⟩ := (contains_iff_entry env condensed table ixe n).mp hc
      exact ⟨.direct e.cause, e.name, e, he, rfl, rfl, (published_congr same).mpr pub⟩
  obtain ⟨reason, hr⟩ := classified
  obtain ⟨r, hr, addr, _⟩ := select_complete hr
  exact ⟨r, hr, addr⟩

/-- Reuse the actual report's blocks/table; this wrapper never recompiles. -/
def selectCompile (env : Ix.Environment) (condensed : Ix.CondensedBlocks)
    (table : Ix.AuxGen.AuxTable) (sub : Ix.Environment) (ixe : Ixon.Env) : List Root :=
  select env (Ix.Compile.ChangedSet.ofCompile (logicalInput env) condensed table ixe) sub ixe

/-- Ordinary selected roots are in the exact Source cone, not a whole-store fallback. -/
theorem selected_input_required_ofCompile {env condensed table sub ixe r}
    (selected : r ∈ selectCompile env condensed table sub ixe) (input : r.reason ≠ .row) :
    RequiredRoot env (Ix.Compile.ChangedSet.ofCompile (logicalInput env) condensed table ixe)
      sub ixe r.address := by
  obtain ⟨n, a, reason⟩ := r
  have classified := select_sound selected
  cases reason with
  | direct cause =>
    obtain ⟨e, he, _, hn, pub⟩ := classified
    refine ⟨n, pub, n, .root (by simp), ?_⟩
    exact (contains_iff_entry env condensed table ixe n).mpr ⟨e, he, by simp [hn]⟩
  | cascade => exact ⟨n, classified.1, classified.2.1⟩
  | row => exact False.elim (input rfl)

end Ix.Cert.SelectedRoots
