import Ix.IxVM.Refinement.Claim
import IxC.Kernel.Ingress.Records
import IxC.Kernel.Verify.Cached.Reference

/-! # The kernel's admission of a role table, executed

`IxVM.consistent` covers a claim under the default role table or under a role table
the kernel admits (`IxVM.Refinement.TableAdmitted`): the table's section admits
(`admitBinding`), and the strict fold accepts, behind the committed prelude, the
closure of the constants the table binds (but for the compiler-trust roles) and of
the theorems its evidence names, with the role specifications the fold does not
check on its own (`BindingSpecs`). `check b E` decides that over the records of
`E`; `tableAdmitted_of_check` proves that a `true` answer establishes
`TableAdmitted` for every view holding `E`.

The proof does not follow how the check finds the closure's order. The check
builds a candidate (`candidate`: a search over the closure's edges that records
how it reached each record, then a depth-first order over the records'
references) and verifies it (`checkAt`):

* `orderedCheck`: the order lists each record once, and none before a record it
  references;
* `closedCheck`: every stored seed is listed, and every edge from a listed record
  lands in the list;
* `reachCheck`: every listed record is reached: each entry of the search's list
  is a stored seed or the target of an edge from an earlier entry.

Together they give `Ix.Cert.ClosureOrderAt` (`closureOrderAt_of_checks`). A wrong
candidate makes the answer `false`, never a wrong `true`. The edges are listed
exactly (`mem_targets`: `targets` holds the targets of `RecordEdge`,
`GroundEdgeAt` and `RecursorEdge` from a record, and nothing else).

The declarations are checked by the executed fold (`Cached.checkDecls`, which
`checkDecls_refines_ref` refines to the pure fold), and, by the pure checker at
the standard fuel, what the fold does not establish itself: every theorem's
statement is a proposition (`TheoremsInProp`) and every role specified by
equations passes `eqnsCheck`.

Nothing here is part of the trusted statement, which mentions only
`TableAdmitted`. -/

namespace Ix.Cert.TableAdmission

open Ix.Kernel
open Ix.Kernel.Admission (Binding Limits)

universe w

/-! ## Sets of addresses -/

/-- The set of a list's addresses. -/
def setOf (l : List Address) : Std.HashSet Address :=
  l.foldl (fun s a => s.insert a) ∅

theorem contains_foldl_insert : ∀ (l : List Address) (s : Std.HashSet Address) (x : Address),
    (l.foldl (fun s a => s.insert a) s).contains x = true ↔ x ∈ l ∨ s.contains x = true
  | [], s, x => by simp
  | a :: l, s, x => by
    rw [List.foldl_cons, contains_foldl_insert l (s.insert a) x, Std.HashSet.contains_insert,
      Bool.or_eq_true, beq_iff_eq, List.mem_cons]
    constructor
    · rintro (h | rfl | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr h
    · rintro ((rfl | h) | h)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

theorem contains_setOf {l : List Address} {x : Address} :
    (setOf l).contains x = true ↔ x ∈ l := by
  rw [setOf, contains_foldl_insert]
  simp

/-! ## The seeds -/

/-- The theorem an evidence entry names, if any. -/
def proofOf? : Evidence Address → Option Address
  | .proof a => some a
  | .defeq => none

/-- **A role table's seeds, listed** (`BindingSeeds`): the constants it binds, but
for the compiler-trust roles, and the theorems its evidence names. -/
def seedList (t : RoleTable) : List Address :=
  ((Role.all.filter fun r => !IxVM.Refinement.compilerTrust r).filterMap t.addressOf?) ++
    t.evidence.toList.flatMap fun e => e.2.toList.filterMap proofOf?

theorem mem_seedList {t : RoleTable} {a : Address} :
    a ∈ seedList t ↔ IxVM.Refinement.BindingSeeds t a := by
  unfold seedList IxVM.Refinement.BindingSeeds
  rw [List.mem_append, List.mem_filterMap, List.mem_flatMap]
  constructor
  · rintro (⟨r, hr, h⟩ | ⟨e, he, hx⟩)
    · rw [List.mem_filter] at hr
      exact Or.inl ⟨r, by simpa using hr.2, h⟩
    · simp only [List.mem_filterMap] at hx
      obtain ⟨x, hx, h⟩ := hx
      cases x with
      | proof c =>
        simp only [proofOf?, Option.some.injEq] at h
        subst h
        exact Or.inr ⟨e, he, hx⟩
      | defeq => simp [proofOf?] at h
  · rintro (⟨r, hr, h⟩ | ⟨e, he, hx⟩)
    · exact Or.inl ⟨r, List.mem_filter.mpr ⟨Role.mem_all r, by simp [hr]⟩, h⟩
    · exact Or.inr ⟨e, he, List.mem_filterMap.mpr ⟨.proof a, hx, rfl⟩⟩

/-! ## The closure's edges, listed -/

/-- The records a `RecordEdge` leads to from `a`: its block, if `a` is a
projection, and the stored records of its reference table. -/
def recordTargets (E : Ixon.Env) (a : Address) : List Address :=
  match recordAt E a with
  | some c =>
    (if ownerOf a c = a then [] else [ownerOf a c]) ++
      c.refs.toList.filter fun b => E.consts.contains b
  | none => []

theorem mem_recordTargets {E : Ixon.Env} {a b : Address} :
    b ∈ recordTargets E a ↔ RecordEdge E a b := by
  unfold recordTargets RecordEdge
  cases hc : recordAt E a with
  | none => simp
  | some c =>
    simp only [Option.some.injEq, exists_eq_left', List.mem_append, List.mem_filter,
      Array.mem_toList_iff, Array.contains_iff_mem]
    constructor
    · rintro (h | h)
      · refine Or.inl ?_
        by_cases ho : ownerOf a c = a
        · rw [ite_eq_left ho] at h
          simp at h
        · rw [ite_eq_right ho, List.mem_singleton] at h
          subst h
          exact ⟨rfl, ho⟩
      · exact Or.inr h
    · rintro (⟨hb, hne⟩ | h)
      · refine Or.inl ?_
        subst hb
        rw [ite_eq_right hne, List.mem_singleton]
      · exact Or.inr h

/-- `p` is `a`, or a projection of the block at `a`. -/
def ownedBy (E : Ixon.Env) (p a : Address) : Bool :=
  decide (p = a) ||
    match recordAt E p with
    | some c => decide (ownerOf p c = a)
    | none => false

theorem ownedBy_iff {E : Ixon.Env} {p a : Address} :
    ownedBy E p a = true ↔ (p = a ∨ ∃ c, recordAt E p = some c ∧ ownerOf p c = a) := by
  unfold ownedBy
  cases recordAt E p <;> simp

/-- The certificate ground of the table's `Nat` operations: each role a bound
operation's install reads (`groundRoles`), with the operation's address. -/
def groundPairs (t : RoleTable) : List (Role × Address) :=
  Role.all.flatMap fun r =>
    match t.addressOf? r with
    | some p => (groundRoles r).map (·, p)
    | none => []

theorem mem_groundPairs {t : RoleTable} {s : Role} {p : Address} :
    (s, p) ∈ groundPairs t ↔ ∃ r, t.addressOf? r = some p ∧ s ∈ groundRoles r := by
  unfold groundPairs
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨r, -, h⟩
    revert h
    cases ha : t.addressOf? r with
    | none => simp
    | some p' =>
      intro h
      simp only [List.mem_map, Prod.mk.injEq] at h
      obtain ⟨s', hs', rfl, rfl⟩ := h
      exact ⟨r, ha, hs'⟩
  · rintro ⟨r, ha, hs⟩
    refine ⟨r, Role.mem_all r, ?_⟩
    simp only [ha, List.mem_map]
    exact ⟨s, hs, rfl⟩

/-- The roles in the certificate ground of an operation whose record is `a` or
projects from `a`. -/
def groundRolesAt (t : RoleTable) (E : Ixon.Env) (a : Address) : List Role :=
  (groundPairs t).filterMap fun sp => if ownedBy E sp.2 a = true then some sp.1 else none

theorem mem_groundRolesAt {t : RoleTable} {E : Ixon.Env} {a : Address} {s : Role} :
    s ∈ groundRolesAt t E a ↔
      ∃ r p, t.addressOf? r = some p ∧ s ∈ groundRoles r ∧
        (p = a ∨ ∃ c, recordAt E p = some c ∧ ownerOf p c = a) := by
  unfold groundRolesAt
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨s', p⟩, hm, h⟩
    dsimp only at h
    by_cases ho : ownedBy E p a = true
    · rw [ite_eq_left ho] at h
      cases h
      obtain ⟨r, ha, hs⟩ := mem_groundPairs.mp hm
      exact ⟨r, p, ha, hs, ownedBy_iff.mp ho⟩
    · rw [ite_eq_right ho] at h
      cases h
  · rintro ⟨r, p, ha, hs, ho⟩
    refine ⟨(s, p), mem_groundPairs.mpr ⟨r, ha, hs⟩, ?_⟩
    dsimp only
    rw [ite_eq_left (ownedBy_iff.mpr ho)]

/-- The roles a record's literals are checked against (`literalRoles`). -/
def litRoles (E : Ixon.Env) (a : Address) : List Role :=
  match recordAt E a with
  | some c => literalRoles c
  | none => []

theorem mem_litRoles {E : Ixon.Env} {a : Address} {s : Role} :
    s ∈ litRoles E a ↔ ∃ c, recordAt E a = some c ∧ s ∈ literalRoles c := by
  unfold litRoles
  cases recordAt E a <;> simp

/-- The record of the role `s`, if it is stored and the target of a
`GroundEdgeAt` from a record whose ground roles are `gr` and literal roles
`lits`. -/
def groundTarget? (t : RoleTable) (E : Ixon.Env) (lits gr : List Role) (s : Role) :
    Option Address :=
  match t.addressOf? s with
  | some b => if E.consts.contains b = true ∧ (s ∈ gr ∨ s ∈ lits) then some b else none
  | none => none

theorem groundTarget?_eq_some {t : RoleTable} {E : Ixon.Env} {lits gr : List Role} {s : Role}
    {b : Address} :
    groundTarget? t E lits gr s = some b ↔
      t.addressOf? s = some b ∧ E.consts.contains b = true ∧ (s ∈ gr ∨ s ∈ lits) := by
  unfold groundTarget?
  cases t.addressOf? s with
  | none => simp
  | some b' =>
    dsimp only
    by_cases hc : E.consts.contains b' = true ∧ (s ∈ gr ∨ s ∈ lits)
    · rw [ite_eq_left hc]
      constructor
      · intro hb
        cases hb
        exact ⟨rfl, hc⟩
      · rintro ⟨hb, -⟩
        exact hb
    · rw [ite_eq_right hc]
      constructor
      · intro hb
        cases hb
      · rintro ⟨hb, hc'⟩
        cases hb
        exact absurd hc' hc

/-- The records a `GroundEdgeAt` leads to from `a`. -/
def groundTargets (t : RoleTable) (E : Ixon.Env) (a : Address) : List Address :=
  let lits := litRoles E a
  let gr := groundRolesAt t E a
  Role.all.filterMap (groundTarget? t E lits gr)

theorem mem_groundTargets {t : RoleTable} {E : Ixon.Env} {a b : Address} :
    b ∈ groundTargets t E a ↔ GroundEdgeAt t E a b := by
  unfold groundTargets GroundEdgeAt
  simp only [List.mem_filterMap, groundTarget?_eq_some, mem_litRoles, mem_groundRolesAt]
  constructor
  · rintro ⟨s, -, hs, hc, h⟩
    exact ⟨hc, s, hs, h⟩
  · rintro ⟨hc, s, hs, h⟩
    exact ⟨s, Role.mem_all s, hs, hc, h⟩

/-- The records a `RecursorEdge` leads to from `a`: the stored recursor records of
the block at `a`, in the recursor index `idx`. -/
def recursorTargets (idx : Reader.RecIndex) (E : Ixon.Env) (a : Address) : List Address :=
  match idx.blocks[a]? with
  | some shape =>
    (shape.recs.toList.map (·.block)).filter fun b => E.consts.contains b && decide (b ≠ a)
  | none => []

theorem mem_recursorTargets {E : Ixon.Env} {a b : Address} :
    b ∈ recursorTargets (artifactRecIndex E) E a ↔ RecursorEdge E a b := by
  unfold recursorTargets RecursorEdge
  cases (artifactRecIndex E).blocks[a]? with
  | none => simp
  | some shape =>
    simp only [List.mem_filter, List.mem_map, Array.mem_toList_iff, Bool.and_eq_true,
      decide_eq_true_eq, Option.some.injEq, exists_eq_left']
    constructor
    · rintro ⟨⟨r, hr, rfl⟩, hc, hne⟩
      exact ⟨hc, hne, r, hr, rfl⟩
    · rintro ⟨hc, hne, r, hr, rfl⟩
      exact ⟨⟨r, hr, rfl⟩, hc, hne⟩

/-- **An edge of a compiled closure** (`CompiledReachAt`'s three steps). -/
def Edge (t : RoleTable) (E : Ixon.Env) (a b : Address) : Prop :=
  RecordEdge E a b ∨ GroundEdgeAt t E a b ∨ RecursorEdge E a b

/-- **The edges from `a`, listed**, with `idx` the recursor index of `E`. -/
def targets (t : RoleTable) (E : Ixon.Env) (idx : Reader.RecIndex) (a : Address) :
    List Address :=
  recordTargets E a ++ groundTargets t E a ++ recursorTargets idx E a

theorem mem_targets {t : RoleTable} {E : Ixon.Env} {a b : Address} :
    b ∈ targets t E (artifactRecIndex E) a ↔ Edge t E a b := by
  unfold targets Edge
  rw [List.mem_append, List.mem_append, mem_recordTargets, mem_groundTargets,
    mem_recursorTargets, or_assoc]

theorem reach_edge {t : RoleTable} {E : Ixon.Env} {S : Address → Prop} {a b : Address}
    (h : CompiledReachAt t E S a) (he : Edge t E a b) : CompiledReachAt t E S b := by
  rcases he with he | he | he
  · exact .step h he
  · exact .ground h he
  · exact .recursor h he

/-! ## Checking a candidate order -/

/-- The records the references of the record at `a` resolve to (`RecordRef`'s
targets, and possibly `a`). -/
def refOwners (E : Ixon.Env) (a : Address) : List Address :=
  match recordAt E a with
  | some c => c.refs.toList.filterMap fun r => (recordAt E r).map (ownerOf r)
  | none => []

theorem mem_refOwners {E : Ixon.Env} {a b : Address} (h : RecordRef E a b) :
    b ∈ refOwners E a := by
  obtain ⟨c, hc, r, hr, cr, hcr, hb, -⟩ := h
  simp only [refOwners, hc]
  exact List.mem_filterMap.mpr ⟨r, Array.mem_toList_iff.mpr hr, by simp [hcr, hb]⟩

/-- One step of `orderedCheck`, from the end of the order: `a` is new, and none of
the records it references comes later. -/
def orderedStep (E : Ixon.Env) (acc : Option (Std.HashSet Address)) (a : Address) :
    Option (Std.HashSet Address) :=
  match acc with
  | none => none
  | some s =>
    if s.contains a = true ∨ (refOwners E a).any s.contains = true then none
    else some (s.insert a)

/-- **The order lists each record once, none before a record it references.** -/
def orderedCheck (E : Ixon.Env) (order : List Address) : Bool :=
  (order.reverse.foldl (orderedStep E) (some ∅)).isSome

theorem foldl_orderedStep_none (E : Ixon.Env) :
    ∀ l : List Address, l.foldl (orderedStep E) none = none
  | [] => rfl
  | _ :: l => foldl_orderedStep_none E l

theorem ordered_of_foldl (E : Ixon.Env) :
    ∀ (l : List Address) (s : Std.HashSet Address),
      l.reverse.foldl (orderedStep E) (some ∅) = some s →
        (∀ x, s.contains x = true ↔ x ∈ l) ∧ l.Nodup ∧
          l.Pairwise fun a b => ¬ RecordRef E a b
  | [], s, h => by
    simp only [List.reverse_nil, List.foldl_nil, Option.some.injEq] at h
    subst h
    exact ⟨fun x => by simp, List.nodup_nil, List.Pairwise.nil⟩
  | a :: l, s, h => by
    rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil] at h
    revert h
    cases hl : l.reverse.foldl (orderedStep E) (some ∅) with
    | none => simp [orderedStep]
    | some s' =>
      obtain ⟨hs', hnd, hpw⟩ := ordered_of_foldl E l s' hl
      intro h
      simp only [orderedStep] at h
      by_cases hc : s'.contains a = true ∨ (refOwners E a).any s'.contains = true
      · rw [ite_eq_left hc] at h
        cases h
      · rw [ite_eq_right hc] at h
        cases h
        have ha : a ∉ l := fun hm => hc (Or.inl ((hs' a).mpr hm))
        refine ⟨?_, List.nodup_cons.mpr ⟨ha, hnd⟩, List.pairwise_cons.mpr ⟨?_, hpw⟩⟩
        · intro x
          rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, hs' x, List.mem_cons]
          exact ⟨fun h => h.imp (fun e => e.symm) id, fun h => h.imp (fun e => e.symm) id⟩
        · intro b hb href
          exact hc (Or.inr (List.any_eq_true.mpr ⟨b, mem_refOwners href, (hs' b).mpr hb⟩))

theorem ordered_of_check {E : Ixon.Env} {order : List Address}
    (h : orderedCheck E order = true) :
    order.Nodup ∧ order.Pairwise fun a b => ¬ RecordRef E a b := by
  revert h
  unfold orderedCheck
  cases hf : order.reverse.foldl (orderedStep E) (some ∅) with
  | none => simp
  | some s => exact fun _ => (ordered_of_foldl E order s hf).2

/-- **The order is closed**: every stored seed is listed, and every edge from a
listed record lands in the list. -/
def closedCheck (t : RoleTable) (E : Ixon.Env) (idx : Reader.RecIndex)
    (seeds order : List Address) : Bool :=
  let listed := setOf order
  (seeds.all fun a => !E.consts.contains a || listed.contains a) &&
    order.all fun a => (targets t E idx a).all listed.contains

theorem mem_of_reach {t : RoleTable} {E : Ixon.Env} {S : Address → Prop}
    {seeds order : List Address} (hS : ∀ a, a ∈ seeds ↔ S a)
    (h : closedCheck t E (artifactRecIndex E) seeds order = true) :
    ∀ a, CompiledReachAt t E S a → a ∈ order := by
  unfold closedCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hseeds, hclosed⟩ := h
  intro a hr
  induction hr with
  | seed hs hc =>
    have := hseeds _ ((hS _).mpr hs)
    rw [hc, Bool.not_true, Bool.false_or, contains_setOf] at this
    exact this
  | step _ he ih =>
    exact contains_setOf.mp (hclosed _ ih _ (mem_targets.mpr (Or.inl he)))
  | ground _ he ih =>
    exact contains_setOf.mp (hclosed _ ih _ (mem_targets.mpr (Or.inr (Or.inl he))))
  | recursor _ he ih =>
    exact contains_setOf.mp (hclosed _ ih _ (mem_targets.mpr (Or.inr (Or.inr he))))

/-- One step of `reachCheck`: the entry is a stored seed (no parent), or the target
of an edge from its parent, an earlier entry. -/
def reachStep (t : RoleTable) (E : Ixon.Env) (idx : Reader.RecIndex) (seeds : List Address)
    (acc : Option (Std.HashSet Address)) (p : Address × Option Address) :
    Option (Std.HashSet Address) :=
  match acc with
  | none => none
  | some s =>
    match p.2 with
    | none =>
      if seeds.contains p.1 = true ∧ E.consts.contains p.1 = true then some (s.insert p.1)
      else none
    | some a =>
      if s.contains a = true ∧ (targets t E idx a).contains p.1 = true then some (s.insert p.1)
      else none

/-- **Every listed record is reached**, along the search's list `wit`. -/
def reachCheck (t : RoleTable) (E : Ixon.Env) (idx : Reader.RecIndex) (seeds : List Address)
    (wit : List (Address × Option Address)) (order : List Address) : Bool :=
  (wit.foldl (reachStep t E idx seeds) (some ∅)).any fun s => order.all s.contains

theorem foldl_reachStep_none {t : RoleTable} {E : Ixon.Env} {idx : Reader.RecIndex}
    {seeds : List Address} :
    ∀ l : List (Address × Option Address), l.foldl (reachStep t E idx seeds) none = none
  | [] => rfl
  | _ :: l => foldl_reachStep_none l

theorem reach_of_foldl {t : RoleTable} {E : Ixon.Env} {S : Address → Prop} {seeds : List Address}
    (hS : ∀ a, a ∈ seeds ↔ S a) :
    ∀ (l : List (Address × Option Address)) (s₀ s : Std.HashSet Address),
      (∀ x, s₀.contains x = true → CompiledReachAt t E S x) →
      l.foldl (reachStep t E (artifactRecIndex E) seeds) (some s₀) = some s →
      ∀ x, s.contains x = true → CompiledReachAt t E S x
  | [], s₀, s, h₀, h => by
    simp only [List.foldl_nil, Option.some.injEq] at h
    subst h
    exact h₀
  | (b, par) :: l, s₀, s, h₀, h => by
    rw [List.foldl_cons] at h
    have step : CompiledReachAt t E S b →
        l.foldl (reachStep t E (artifactRecIndex E) seeds) (some (s₀.insert b)) = some s →
        ∀ x, s.contains x = true → CompiledReachAt t E S x := by
      intro hb hl
      refine reach_of_foldl hS l (s₀.insert b) s ?_ hl
      intro x hx
      rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
      rcases hx with rfl | hx
      · exact hb
      · exact h₀ x hx
    cases par with
    | none =>
      simp only [reachStep] at h
      by_cases hc : seeds.contains b = true ∧ E.consts.contains b = true
      · rw [ite_eq_left hc] at h
        exact step (.seed ((hS _).mp (List.contains_iff_mem.mp hc.1)) hc.2) h
      · rw [ite_eq_right hc, foldl_reachStep_none] at h
        cases h
    | some a =>
      simp only [reachStep] at h
      by_cases hc : s₀.contains a = true ∧
          (targets t E (artifactRecIndex E) a).contains b = true
      · rw [ite_eq_left hc] at h
        exact step (reach_edge (h₀ a hc.1) (mem_targets.mp (List.contains_iff_mem.mp hc.2))) h
      · rw [ite_eq_right hc, foldl_reachStep_none] at h
        cases h

/-- **The three checks give the closure order.** -/
theorem closureOrderAt_of_checks {t : RoleTable} {E : Ixon.Env} {S : Address → Prop}
    {seeds order : List Address} {wit : List (Address × Option Address)}
    (hS : ∀ a, a ∈ seeds ↔ S a) (hord : orderedCheck E order = true)
    (hcl : closedCheck t E (artifactRecIndex E) seeds order = true)
    (hreach : reachCheck t E (artifactRecIndex E) seeds wit order = true) :
    ClosureOrderAt t E S order := by
  obtain ⟨hnd, hpw⟩ := ordered_of_check hord
  refine ⟨hnd, fun a => ⟨fun ha => ?_, mem_of_reach hS hcl a⟩, hpw⟩
  revert hreach
  unfold reachCheck
  cases hf : wit.foldl (reachStep t E (artifactRecIndex E) seeds) (some ∅) with
  | none => simp
  | some s =>
    intro hreach
    have hall : order.all s.contains = true := hreach
    exact reach_of_foldl hS wit ∅ s (fun x hx => by simp at hx) hf a
      (List.all_eq_true.mp hall a ha)

/-! ## Checking the declarations -/

/-- The fuel the pure checker runs at here: the standard one. -/
def pureFuel : Nat := checkFuel

/-- A theorem declaration's statement is a proposition, by the pure checker at
`pureFuel` in the installed environment `envA` (`TheoremsInProp`). -/
def thmInProp (envA : Env .anon) : Declaration .anon → Bool
  | .thmDecl cv _ =>
    match (fueledOps .verified pureFuel).annotate envA 0 cv.type with
    | .ok tA =>
      match (fueledOps .verified pureFuel).inferType envA 0 tA with
      | .ok stype =>
        match (fueledOps .verified pureFuel).ensureSort envA 0 stype with
        | .ok u => u.isZero
        | .error _ => false
      | .error _ => false
    | .error _ => false
  | _ => true

theorem theoremsInProp_of {envA : Env .anon} {ds : List (Declaration .anon)}
    (h : ds.all (thmInProp envA) = true) : IxVM.Refinement.TheoremsInProp envA ds := by
  intro cv value hmem
  have hd := List.all_eq_true.mp h _ hmem
  revert hd
  simp only [thmInProp]
  cases h1 : (fueledOps .verified pureFuel).annotate envA 0 cv.type with
  | error _ => simp
  | ok tA =>
    dsimp only
    cases h2 : (fueledOps .verified pureFuel).inferType envA 0 tA with
    | error _ => simp
    | ok stype =>
      dsimp only
      cases h3 : (fueledOps .verified pureFuel).ensureSort envA 0 stype with
      | error _ => simp
      | ok u => exact fun hd => ⟨pureFuel, tA, stype, u, h1, h2, h3, hd⟩

/-- A declared constant at an anchor role has its specification's type. -/
def anchorTyped (cv : Ix.Kernel.ConstantVal .anon) : Bool :=
  match IxVM.Refinement.anchorPin? cv.name with
  | some pin => cv.matchesPin pin
  | none => true

/-- No declaration mismatches an install-checked anchor, and every declared anchor
has its specification's type. -/
def anchorsOk (ds : List (Declaration .anon)) : Bool :=
  ds.all fun d => d.anchorMismatch?.isNone && (IxVM.Refinement.declaredVals d).all anchorTyped

theorem anchors_of {ds : List (Declaration .anon)} (h : anchorsOk ds = true) :
    (∀ d ∈ ds, d.anchorMismatch? = none) ∧ IxVM.Refinement.AnchorsTyped ds := by
  unfold anchorsOk at h
  rw [List.all_eq_true] at h
  refine ⟨fun d hd => ?_, ?_⟩
  · have hdd := h d hd
    rw [Bool.and_eq_true, Option.isNone_iff_eq_none] at hdd
    exact hdd.1
  · intro d hd cv hcv pin hpin
    have hdd := h d hd
    rw [Bool.and_eq_true, List.all_eq_true] at hdd
    have hc := hdd.2 cv hcv
    simpa only [anchorTyped, hpin] using hc

/-- Whether a computation succeeded. -/
def isOk {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

/-- Every role specified by equations passes `eqnsCheck` at `pureFuel` in the
installed environment, under the evidence `ev`. -/
def eqnsOk (envA : Env .anon) (ev : Evidences .anon) : Bool :=
  Role.all.all fun r => decide ((r.spec (md := .anon)).kind ≠ .eqns) ||
    isOk (eqnsCheck (fueledOps .verified pureFuel) envA r ev)

theorem eqns_of {envA : Env .anon} {ev : Evidences .anon} (h : eqnsOk envA ev = true) :
    ∀ r ∈ Role.all, (r.spec (md := .anon)).kind = .eqns →
      ∃ F, eqnsCheck (fueledOps .verified F) envA r ev = .ok () := by
  intro r hr hk
  have hor := List.all_eq_true.mp h r hr
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hor
  rcases hor with hne | hok
  · exact absurd hk hne
  · revert hok
    cases hc : eqnsCheck (fueledOps .verified pureFuel) envA r ev with
    | error _ => simp [isOk]
    | ok u => exact fun _ => ⟨pureFuel, hc⟩

/-- **What the fold does not check on its own**, decided: theorems' statements are
propositions, no user axiom is declared, and the role specifications hold. -/
def declsOk (envA : Env .anon) (ev : Evidences .anon) (ds : List (Declaration .anon)) : Bool :=
  ds.all (thmInProp envA) && (userAxiomsOfDecls ds).isEmpty && anchorsOk ds && eqnsOk envA ev

theorem declsOk_sound {b : Binding} {envA : Env .anon} {ev : Evidences .anon}
    {ds : List (Declaration .anon)} (h : declsOk envA ev ds = true) :
    IxVM.Refinement.TheoremsInProp envA ds ∧ IxVM.Refinement.UserAxiomsWithin (fun _ => False) ds ∧
      IxVM.Refinement.BindingSpecs b envA ds := by
  unfold declsOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hthm, hax⟩, hanc⟩, heqns⟩ := h
  rw [List.isEmpty_iff] at hax
  obtain ⟨hmis, htyped⟩ := anchors_of hanc
  refine ⟨theoremsInProp_of hthm, ?_, hmis, htyped, ev, eqns_of heqns⟩
  intro cv hcv
  rw [hax] at hcv
  cases hcv

/-- The coverage limits of the reading (input bounds only). -/
def admissionLimits : Limits := ⟨1 <<< 22, 1 <<< 22, 1 <<< 34, 1 <<< 28, 1 <<< 26⟩

/-- **The reading and the fold accept the records of `order`** under the admitted
table `t` (of the binding `b`), behind its committed prelude, and the installed
environment meets `declsOk`. -/
def preparedOk (b : Binding) (E : Ixon.Env) (t : RoleTable) (order : List Address) : Bool :=
  match (Reader.preludeFor t : Except String (Reader.Prelude .anon)) with
  | .error _ => false
  | .ok pre =>
    match Admission.prepareWith Address.admissionHash b pre admissionLimits (recordsOf E order)
        (blobsOf E order) (hintsOf E) with
    | .error _ => false
    | .ok (ev, ds) =>
      match Cached.checkDecls .verified ev (ds.map IxVM.Refinement.thmToOpaqueDefn) with
      | .error _ => false
      | .ok envA => declsOk envA ev ds.toList

theorem preparedOk_sound (W : Type w) [SetTheory W] {b : Binding} {E : Ixon.Env}
    {t : RoleTable} {order : List Address} (h : preparedOk b E t order = true) :
    ∃ (pre : Reader.Prelude .anon) (ev : Evidences .anon) (ds : Array (Declaration .anon))
      (envA : Env .anon), Reader.preludeFor t = .ok pre ∧
      Admission.prepareWith Address.admissionHash b pre admissionLimits (recordsOf E order)
        (blobsOf E order) (hintsOf E) = .ok (ev, ds) ∧
      Cached.AcceptsRefUnder .strict .verified ev
        (ds.toList.map IxVM.Refinement.thmToOpaqueDefn) envA ∧
      IxVM.Refinement.TheoremsInProp envA ds.toList ∧
      IxVM.Refinement.UserAxiomsWithin (fun _ => False) ds.toList ∧
      IxVM.Refinement.BindingSpecs b envA ds.toList := by
  unfold preparedOk at h
  split at h
  · exact absurd h Bool.false_ne_true
  · rename_i pre hpre
    split at h
    · exact absurd h Bool.false_ne_true
    · rename_i ev ds hprep
      split at h
      · exact absurd h Bool.false_ne_true
      · rename_i envA hck
        have href := Cached.checkDecls_refines_ref W rfl hck
        rw [Array.toList_map] at href
        obtain ⟨hthm, hax, hspecs⟩ := declsOk_sound (b := b) h
        exact ⟨pre, ev, ds, envA, hpre, hprep, Cached.acceptsRefUnder_strict.mpr href,
          hthm, hax, hspecs⟩

/-! ## The check -/

/-- An `Ixon.Env` draws from itself. -/
theorem draws_refl (E : Ixon.Env) : IxVM.Refinement.Draws E E :=
  ⟨fun _ lc h => Or.inl ⟨lc, h, rfl⟩, fun _ _ h => h⟩

/-- **The admission of `b`, as the table `t`, over the records of `E`, with the
candidate search list `wit` and order `order`**: the seeds are stored, the order
checks (`orderedCheck`, `closedCheck`, `reachCheck`), and the reading and the
fold accept it (`preparedOk`). `idx` is `E`'s recursor index (`artifactRecIndex`),
passed so that it is computed once. -/
def checkAt (b : Binding) (E : Ixon.Env) (t : RoleTable) (idx : Reader.RecIndex)
    (wit : List (Address × Option Address)) (order : List Address) : Bool :=
  let seeds := seedList t
  seeds.all E.consts.contains && orderedCheck E order && closedCheck t E idx seeds order &&
    reachCheck t E idx seeds wit order && preparedOk b E t order

theorem checkAt_sound (W : Type w) [SetTheory W] {b : Binding} {E : Ixon.Env} {t : RoleTable}
    {idx : Reader.RecIndex} {wit : List (Address × Option Address)} {order : List Address}
    (ht : Admission.admitBinding Address.admissionHash b = .ok t) (hidx : idx = artifactRecIndex E)
    (h : checkAt b E t idx wit order = true) (V : IxVM.Refinement.View) (hV : V.env = E) :
    IxVM.Refinement.TableAdmitted V b := by
  subst hV hidx
  unfold checkAt at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hseeds, hord⟩, hcl⟩, hreach⟩, hprep⟩ := h
  have hS : ∀ a, a ∈ seedList t ↔ IxVM.Refinement.BindingSeeds t a := fun _ => mem_seedList
  obtain ⟨pre, ev, ds, envA, hpre, hprepared, hacc, hthm, hax, hspecs⟩ := preparedOk_sound W hprep
  refine ⟨t, ht, V.env, admissionLimits, order, envA, draws_refl V.env, ?_, t, pre, ev, ds, ht,
    closureOrderAt_of_checks hS hord hcl hreach, rfl, hpre, hprepared, hacc, hthm, hax, hspecs⟩
  intro a ha
  exact List.all_eq_true.mp hseeds a (mem_seedList.mpr ha)

/-! ## A candidate order (not trusted: `checkAt` verifies it) -/

/-- The search's step at the record `a`: every target of an edge from `a` not yet
seen joins the list, with `a` as its parent. -/
def discoverStep (t : RoleTable) (E : Ixon.Env) (idx : Reader.RecIndex)
    (st : Array (Address × Option Address) × Std.HashSet Address) (a : Address) :
    Array (Address × Option Address) × Std.HashSet Address :=
  (targets t E idx a).foldl (fun st b =>
    if st.2.contains b then st else (st.1.push (b, some a), st.2.insert b)) st

/-- The search from position `i` of its list. Every entry is a stored record, so
`E.consts.size + 1` steps suffice. -/
def discoverLoop (t : RoleTable) (E : Ixon.Env) (idx : Reader.RecIndex) :
    Nat → Nat → Array (Address × Option Address) × Std.HashSet Address →
      Array (Address × Option Address)
  | 0, _, st => st.1
  | fuel + 1, i, st =>
    if h : i < st.1.size then discoverLoop t E idx fuel (i + 1) (discoverStep t E idx st st.1[i].1)
    else st.1

/-- The search's list: the stored seeds, then every record reached, each with the
record it was reached from. -/
def discover (t : RoleTable) (E : Ixon.Env) (idx : Reader.RecIndex) (seeds : List Address) :
    Array (Address × Option Address) :=
  let init := seeds.foldl (fun (st : Array (Address × Option Address) × Std.HashSet Address) a =>
    if st.2.contains a || !E.consts.contains a then st else (st.1.push (a, none), st.2.insert a))
    (#[], ∅)
  discoverLoop t E idx (E.consts.size + 1) 0 init

/-- Depth-first postorder from `a` over the records it references, among `nodes`;
an inductive block's recursor records follow it. -/
def visit (E : Ixon.Env) (idx : Reader.RecIndex) (nodes : Std.HashSet Address) :
    Nat → Address → Std.HashSet Address × Array Address → Std.HashSet Address × Array Address
  | 0, _, st => st
  | fuel + 1, a, st =>
    if st.1.contains a || !nodes.contains a then st
    else
      let st := (refOwners E a).foldl (fun st b => visit E idx nodes fuel b st) (st.1.insert a, st.2)
      let st := (st.1, st.2.push a)
      (recursorTargets idx E a).foldl (fun st r => visit E idx nodes fuel r st) st

/-- The records `nodes`, no record before one it references (for an acyclic
reference graph). -/
def topo (E : Ixon.Env) (idx : Reader.RecIndex) (nodes : List Address) : Array Address :=
  let set := setOf nodes
  (nodes.foldl (fun st a => visit E idx set (nodes.length + 1) a st) (∅, #[])).2

/-- **The candidate**: the search's list and an order of the records it reached. -/
def candidate (t : RoleTable) (E : Ixon.Env) (idx : Reader.RecIndex) :
    List (Address × Option Address) × List Address :=
  let wit := (discover t E idx (seedList t)).toList
  (wit, (topo E idx (wit.map (·.1))).toList)

/-- **The kernel's admission of the role table `b` over the records of `E`**,
decided: `b` admits, and the strict fold accepts, behind the committed prelude,
the closure in `E` of the constants the table binds (but for the compiler-trust
roles) and of the theorems its evidence names, with the role specifications
(`BindingSpecs`). `true` establishes `TableAdmitted` for every view holding `E`
(`tableAdmitted_of_check`). The records must be in `E`, recursor records
included. -/
def check (b : Binding) (E : Ixon.Env) : Bool :=
  match Admission.admitBinding Address.admissionHash b with
  | .error _ => false
  | .ok t =>
    let idx := artifactRecIndex E
    let c := candidate t E idx
    checkAt b E t idx c.1 c.2

/-- **A passing check establishes the table's admission** for every view holding
the records, through the fold's refinement (the set theory is a hypothesis of
that walk, not of the statement's meaning). -/
theorem tableAdmitted_of_check (W : Type w) [SetTheory W] {b : Binding} {E : Ixon.Env}
    (h : check b E = true) (V : IxVM.Refinement.View) (hV : V.env = E) :
    IxVM.Refinement.TableAdmitted V b := by
  unfold check at h
  split at h
  · exact absurd h Bool.false_ne_true
  · rename_i t ht
    exact checkAt_sound (wit := (candidate t E (artifactRecIndex E)).1)
      (order := (candidate t E (artifactRecIndex E)).2) W ht rfl h V hV

end Ix.Cert.TableAdmission
