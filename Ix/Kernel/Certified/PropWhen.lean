/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/PropWhen.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.VLevel

/-!
# Checked zero conditions for anonymous universe parameters

A condition is either never true or says that a finite set of parameter
indices are all zero. Strictly increasing lists give one representation for
each finite set. The empty set is the condition that always holds.

These conditions describe only whether a level is zero. They do not identify
levels: for example, `Sort 1` and `Sort 2` both have condition `never`.
The decoder checks bounds independently, including for conditions that are
always false. Level well-formedness must also be checked on the source level.
-/

namespace Ix.Kernel.Certified

namespace IndexSet

def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
    if x < y then x :: y :: ys
    else if x = y then y :: ys
    else y :: insert x ys

@[simp] theorem mem_insert {z x : Nat} {xs : List Nat} :
    z ∈ insert x xs ↔ z = x ∨ z ∈ xs := by
  induction xs with
  | nil => simp [insert]
  | cons y ys ih =>
    simp only [insert]
    split
    · simp
    · split
      · subst x; simp
      · simp only [List.mem_cons, ih, or_left_comm]

theorem sorted_insert {x : Nat} {xs : List Nat}
    (h : xs.Pairwise (· < ·)) : (insert x xs).Pairwise (· < ·) := by
  induction xs with
  | nil => simp [insert]
  | cons y ys ih =>
    obtain ⟨hy, hs⟩ := List.pairwise_cons.mp h
    simp only [insert]
    split
    next hxy =>
      apply List.pairwise_cons.mpr
      exact ⟨fun z hz => (List.mem_cons.mp hz).elim (fun e => e ▸ hxy)
        (fun hz => Nat.lt_trans hxy (hy z hz)), h⟩
    next hxy =>
      split
      · exact h
      next hne =>
        apply List.pairwise_cons.mpr
        refine ⟨?_, ih hs⟩
        intro z hz
        rcases mem_insert.mp hz with rfl | hz
        · omega
        · exact hy z hz

def normalize : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (normalize xs)

@[simp] theorem mem_normalize {z : Nat} {xs : List Nat} :
    z ∈ normalize xs ↔ z ∈ xs := by
  induction xs <;> simp [normalize, *]

theorem sorted_normalize (xs : List Nat) : (normalize xs).Pairwise (· < ·) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact sorted_insert ih

/-- Equality of increasing lists is determined by their members. -/
theorem eq_of_members {xs ys : List Nat}
    (hx : xs.Pairwise (· < ·)) (hy : ys.Pairwise (· < ·))
    (hm : ∀ i, i ∈ xs ↔ i ∈ ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    symm
    exact List.eq_nil_iff_forall_not_mem.mpr fun i hi => by simpa using (hm i).mpr hi
  | cons x xs ih =>
    cases ys with
    | nil => simpa using (hm x).mp (List.mem_cons_self ..)
    | cons y ys =>
      obtain ⟨hxmin, hxs⟩ := List.pairwise_cons.mp hx
      obtain ⟨hymin, hys⟩ := List.pairwise_cons.mp hy
      have hxy : x = y := by
        have hxmem := (hm x).mp (List.mem_cons_self ..)
        have hymem := (hm y).mpr (List.mem_cons_self ..)
        simp only [List.mem_cons] at hxmem hymem
        rcases hxmem with h | h
        · exact h
        rcases hymem with h' | h'
        · exact h'.symm
        have := hxmin y h'
        have := hymin x h
        omega
      subst y
      congr 1
      apply ih hxs hys
      intro i
      have hxi : i ∈ xs → i ≠ x := fun hi e => by
        have := hxmin i hi
        omega
      have hyi : i ∈ ys → i ≠ x := fun hi e => by
        have := hymin i hi
        omega
      specialize hm i
      simp only [List.mem_cons] at hm
      by_cases hie : i = x
      · subst i; simp_all
      · simpa [hie] using hm

end IndexSet

inductive PropWhen where
  | never
  | allZero (params : List Nat) (sorted : params.Pairwise (· < ·))
deriving DecidableEq, Repr

namespace PropWhen

def always : PropWhen := .allZero [] .nil

def ofList (params : List Nat) : PropWhen :=
  .allZero (IndexSet.normalize params) (IndexSet.sorted_normalize params)

def param (i : Nat) : PropWhen := .allZero [i] (by simp)

def toRaw : PropWhen → Option (List Nat)
  | .never => none
  | .allZero ps _ => some ps

theorem toRaw_injective {p q : PropWhen} (h : p.toRaw = q.toRaw) : p = q := by
  cases p <;> cases q <;> simp_all [toRaw]

def holds (valuation : Nat → Nat) : PropWhen → Bool
  | .never => false
  | .allZero ps _ => ps.all (valuation · == 0)

@[simp] theorem holds_never (v : Nat → Nat) : holds v .never = false := rfl

@[simp] theorem holds_always (v : Nat → Nat) : holds v always = true := rfl

@[simp] theorem holds_param (v : Nat → Nat) (i : Nat) :
    holds v (param i) = (v i == 0) := by simp [holds, param]

@[simp] theorem holds_ofList (v : Nat → Nat) (ps : List Nat) :
    holds v (ofList ps) = ps.all (v · == 0) := by
  apply Bool.eq_iff_iff.mpr
  simp [holds, ofList, List.all_eq_true]

private theorem holds_separator (ps : List Nat) (hs : ps.Pairwise (· < ·)) (i : Nat) :
    holds (fun j => if j = i then 1 else 0) (.allZero ps hs) = decide (i ∉ ps) := by
  apply Bool.eq_iff_iff.mpr
  simp only [holds, List.all_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h hi
    have := h i hi
    simp at this
  · intro h j hj
    have hji : j ≠ i := fun e => h (e ▸ hj)
    simp [hji]

/-- The representation is canonical, including the distinction between
`never` and a nonempty set of zero requirements. -/
theorem eq_of_holds {p q : PropWhen}
    (h : ∀ v : Nat → Nat, holds v p = holds v q) : p = q := by
  cases p with
  | never =>
    cases q with
    | never => rfl
    | allZero qs hq => simpa [holds] using h (fun _ => 0)
  | allZero ps hp =>
    cases q with
    | never => simpa [holds] using h (fun _ => 0)
    | allZero qs hq =>
      have hm : ∀ i, i ∈ ps ↔ i ∈ qs := by
        intro i
        have hi := h (fun j => if j = i then 1 else 0)
        rw [holds_separator, holds_separator] at hi
        have hn : i ∉ ps ↔ i ∉ qs := by simpa using Bool.eq_iff_iff.mp hi
        by_cases hp' : i ∈ ps <;> by_cases hq' : i ∈ qs <;> simp_all
      have := IndexSet.eq_of_members hp hq hm
      subst qs
      rfl

theorem eq_iff_holds (p q : PropWhen) :
    p = q ↔ ∀ v : Nat → Nat, holds v p = holds v q :=
  ⟨fun h _ => h ▸ rfl, eq_of_holds⟩

/-- All named parameters are in scope; this is separate from the zero test. -/
def WF (n : Nat) : PropWhen → Prop
  | .never => True
  | .allZero ps _ => ∀ i ∈ ps, i < n

instance {n : Nat} {p : PropWhen} : Decidable (WF n p) := by
  cases p <;> unfold WF <;> infer_instance

/-- Decode the canonical representation. Malformed ordering and out-of-range
indices are rejected, rather than silently normalized or defaulted to zero. -/
def fromRaw? (n : Nat) : Option (List Nat) → Option PropWhen
  | none => some .never
  | some ps =>
    if hs : ps.Pairwise (· < ·) then
      if ∀ i ∈ ps, i < n then some (.allZero ps hs) else none
    else none

theorem fromRaw?_sound {n : Nat} {raw : Option (List Nat)} {p : PropWhen}
    (h : fromRaw? n raw = some p) : p.toRaw = raw ∧ p.WF n := by
  cases raw with
  | none => simp [fromRaw?] at h; subst p; simp [toRaw, WF]
  | some ps =>
    simp only [fromRaw?] at h
    split at h
    · split at h
      next hb => cases h; exact ⟨rfl, hb⟩
      · contradiction
    · contradiction

theorem fromRaw?_complete {n : Nat} {p : PropWhen} (h : p.WF n) :
    fromRaw? n p.toRaw = some p := by
  cases p with
  | never => rfl
  | allZero ps hs => simp_all [fromRaw?, toRaw, WF]

def inter : PropWhen → PropWhen → PropWhen
  | .allZero ps _, .allZero qs _ => ofList (ps ++ qs)
  | _, _ => .never

@[simp] theorem holds_inter (v : Nat → Nat) (p q : PropWhen) :
    holds v (inter p q) = (holds v p && holds v q) := by
  apply Bool.eq_iff_iff.mpr
  cases p <;> cases q <;>
    simp [inter, holds, ofList, List.all_eq_true, or_imp, forall_and]

theorem inter_comm (p q : PropWhen) : inter p q = inter q p := by
  apply eq_of_holds; intro v; simp [Bool.and_comm]

theorem inter_assoc (p q r : PropWhen) : inter (inter p q) r = inter p (inter q r) := by
  apply eq_of_holds; intro v; simp [Bool.and_assoc]

@[simp] theorem inter_always (p : PropWhen) : inter p always = p := by
  apply eq_of_holds; intro v; simp

@[simp] theorem always_inter (p : PropWhen) : inter always p = p := by
  rw [inter_comm, inter_always]

@[simp] theorem inter_self (p : PropWhen) : inter p p = p := by
  apply eq_of_holds; intro v; simp

theorem WF.inter {n : Nat} {p q : PropWhen} (hp : p.WF n) (hq : q.WF n) :
    (p.inter q).WF n := by
  cases p <;> cases q <;>
    simp_all [PropWhen.inter, ofList, PropWhen.WF, or_imp]

def bindList (f : Nat → PropWhen) : List Nat → PropWhen
  | [] => always
  | i :: ps => inter (f i) (bindList f ps)

def bind (f : Nat → PropWhen) : PropWhen → PropWhen
  | .never => .never
  | .allZero ps _ => bindList f ps

theorem holds_bindList (v : Nat → Nat) (f : Nat → PropWhen) (ps : List Nat) :
    holds v (bindList f ps) = ps.all (fun i => holds v (f i)) := by
  induction ps <;> simp [bindList, *]

theorem holds_bind (v : Nat → Nat) (f : Nat → PropWhen) (p : PropWhen) :
    holds v (bind f p) = holds (fun i => if holds v (f i) then 0 else 1) p := by
  cases p with
  | never => rfl
  | allZero ps hs =>
    change holds v (bindList f ps) =
      ps.all (fun i => (if holds v (f i) then 0 else 1) == 0)
    rw [holds_bindList]
    apply List.all_congr rfl
    intro i
    cases holds v (f i) <;> rfl

theorem holds_bind_of (v w : Nat → Nat) (f : Nat → PropWhen) (p : PropWhen)
    (h : ∀ i, holds v (f i) = (w i == 0)) : holds v (bind f p) = holds w p := by
  cases p with
  | never => rfl
  | allZero ps hs =>
    change holds v (bindList f ps) = ps.all (w · == 0)
    rw [holds_bindList]
    exact List.all_congr rfl h

@[simp] theorem bind_never (f : Nat → PropWhen) : bind f .never = .never := rfl

@[simp] theorem bind_always (f : Nat → PropWhen) : bind f always = always := rfl

@[simp] theorem bind_param (f : Nat → PropWhen) (i : Nat) : bind f (param i) = f i := by
  simp [bind, param, bindList]

theorem bind_inter (f : Nat → PropWhen) (p q : PropWhen) :
    bind f (inter p q) = inter (bind f p) (bind f q) := by
  apply eq_of_holds
  intro v
  simp only [holds_bind, holds_inter]

@[simp] theorem bind_id (p : PropWhen) : bind param p = p := by
  apply eq_of_holds
  intro v
  exact holds_bind_of v v param p (fun i => holds_param v i)

theorem bindList_wf {n : Nat} {f : Nat → PropWhen} {ps : List Nat}
    (h : ∀ i ∈ ps, (f i).WF n) : (bindList f ps).WF n := by
  induction ps with
  | nil => simp [bindList, always, WF]
  | cons i ps ih =>
    exact WF.inter (h i (by simp)) (ih fun j hj => h j (by simp [hj]))

theorem WF.bind {n k : Nat} {f : Nat → PropWhen} {p : PropWhen}
    (hp : p.WF k) (h : ∀ i, i < k → (f i).WF n) : (bind f p).WF n := by
  cases p with
  | never => trivial
  | allZero ps hs => exact bindList_wf fun i hi => h i (hp i hi)

end PropWhen

end Ix.Kernel.Certified
