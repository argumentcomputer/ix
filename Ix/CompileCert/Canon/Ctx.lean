import Ix.CompileCert.Canon.Ref
import Ix.Mutual

/-! # The class context `MutConst.ctx`

`Ix.MutConst.ctx classes` maps each member to the
index of its class and each constructor to `#classes + offset + position`,
the offsets reserved per class by the class's largest constructor count.
This module reads the imperative definition as a fold of insertions of an
explicit list of pairs (`ctx_eq`, `ctxPairs`) and, when the member and
constructor names are pairwise distinct (`KeysDistinct`),
proves:

* `ctx_member`, `ctx_ctor`: the value of a member's and of a constructor's
  name;
* `ctx_dom`: the names in the context are exactly the member and
  constructor names (as values: the map compares names exactly). -/

namespace Ix.CompileCert.Canon

open Ix (Name MutConst MutCtx ConstructorVal)

/-! ## The definition as a fold -/

/-- One class's step of `MutConst.ctx`. -/
def ctxStep (s : MutCtx × Nat) (p : List MutConst × Nat) : MutCtx × Nat :=
  let r := p.1.foldl (fun s' m => (m.ctors.zipIdx.foldl (fun mc q => mc.insert q.1.cnst.name (s.2 + q.2))
    (s'.1.insert m.name p.2), max s'.2 m.ctors.size)) (s.1, 0)
  (r.1, s.2 + r.2)

theorem ctx_eq (classes : List (List MutConst)) :
    MutConst.ctx classes = (classes.zipIdx.foldl ctxStep (default, classes.length)).1 := by
  simp only [MutConst.ctx]
  delta ctxStep
  simp

/-- Insert a pair. -/
def insP (mc : MutCtx) (p : Name × Nat) : MutCtx := mc.insert p.1 p.2

/-- The largest constructor count of a class. -/
def maxC (C : List MutConst) : Nat := C.foldl (fun mx m => max mx m.ctors.size) 0

theorem foldl_max (C : List MutConst) (mx : Nat) :
    C.foldl (fun mx m => max mx m.ctors.size) mx = max mx (maxC C) := by
  unfold maxC
  induction C generalizing mx with
  | nil => simp
  | cons m C ih =>
    simp only [List.foldl_cons]
    rw [ih, ih (max 0 m.ctors.size)]
    simp only [Nat.zero_max]
    rw [Nat.max_assoc]

/-- The pairs one class inserts: each member at the class index `j`, each constructor of a
member at the class's base `i` plus its position. -/
def pairsOf (j i : Nat) (C : List MutConst) : List (Name × Nat) :=
  C.flatMap fun m => (m.name, j) :: (m.ctors.toList.zipIdx.map fun q => (q.1.cnst.name, i + q.2))

/-- All the pairs, classes from index `n` with constructor base `i`. -/
def ctxPairs : List (List MutConst) → Nat → Nat → List (Name × Nat)
  | [], _, _ => []
  | C :: rest, n, i => pairsOf n i C ++ ctxPairs rest (n + 1) (i + maxC C)

/-- The sum of the classes' largest constructor counts. -/
def sumMaxC : List (List MutConst) → Nat
  | [] => 0
  | C :: rest => maxC C + sumMaxC rest

theorem ctor_fold (i : Nat) (m : MutConst) (mc : MutCtx) :
    m.ctors.zipIdx.foldl (fun mc q => mc.insert q.1.cnst.name (i + q.2)) mc =
      (m.ctors.toList.zipIdx.map fun q => (q.1.cnst.name, i + q.2)).foldl insP mc := by
  rw [← Array.foldl_toList, Array.toList_zipIdx, List.foldl_map]
  rfl

theorem class_fold (i j : Nat) : ∀ (C : List MutConst) (mc : MutCtx) (mx : Nat),
    C.foldl (fun s' m => (m.ctors.zipIdx.foldl (fun mc q => mc.insert q.1.cnst.name (i + q.2))
      (s'.1.insert m.name j), max s'.2 m.ctors.size)) (mc, mx) =
      ((pairsOf j i C).foldl insP mc, max mx (maxC C)) := by
  intro C
  induction C with
  | nil => intro mc mx; simp [pairsOf, maxC]
  | cons m C ih =>
    intro mc mx
    simp only [List.foldl_cons]
    rw [ih, ctor_fold]
    simp only [pairsOf, List.flatMap_cons, List.foldl_append, List.foldl_cons, Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    unfold maxC
    simp only [List.foldl_cons, Nat.zero_max]
    rw [foldl_max, foldl_max, Nat.max_assoc, Nat.zero_max]

theorem classes_fold : ∀ (cls : List (List MutConst)) (n i : Nat) (mc : MutCtx),
    (cls.zipIdx n).foldl ctxStep (mc, i) = ((ctxPairs cls n i).foldl insP mc, i + sumMaxC cls) := by
  intro cls
  induction cls with
  | nil => intro n i mc; simp [ctxPairs, sumMaxC]
  | cons C rest ih =>
    intro n i mc
    simp only [List.zipIdx_cons, List.foldl_cons]
    have hstep : ctxStep (mc, i) (C, n) = ((pairsOf n i C).foldl insP mc, i + maxC C) := by
      unfold ctxStep
      simp only
      rw [class_fold]
      simp
    rw [hstep, ih]
    simp only [ctxPairs, sumMaxC, List.foldl_append, Prod.mk.injEq, true_and]
    omega

theorem ctx_fold (classes : List (List MutConst)) :
    MutConst.ctx classes = (ctxPairs classes 0 classes.length).foldl insP default := by
  rw [ctx_eq]
  have := classes_fold classes 0 classes.length default
  rw [show classes.zipIdx = classes.zipIdx 0 from rfl, this]

/-! ## Lookups in a fold of distinct-key insertions

`MutCtx` is a tree map under `nameCompareExact`, a lawful order whose `eq`
is equality (`Ref.lean`): a lookup after an insertion answers the inserted
value for the inserted name only. -/

theorem treeMap_insert_self (m0 : MutCtx) (k : Name) (v : Nat) : (m0.insert k v)[k]? = some v := by
  rw [Std.TreeMap.getElem?_insert]; simp

theorem treeMap_insert_ne (m0 : MutCtx) {k x : Name} (v : Nat) (h : k ≠ x) :
    (m0.insert k v)[x]? = m0[x]? := by
  rw [Std.TreeMap.getElem?_insert]; simp [h]

theorem foldl_insP_getElem? :
    ∀ (L : List (Name × Nat)) (m0 : MutCtx),
      (L.map (·.1)).Pairwise (· ≠ ·) → ∀ (x : Name) (v : Nat),
      (L.foldl insP m0)[x]? = some v ↔
        (∃ p ∈ L, p.1 = x ∧ p.2 = v) ∨ ((∀ p ∈ L, p.1 ≠ x) ∧ m0[x]? = some v) := by
  intro L
  induction L with
  | nil =>
    intro m0 _ x v
    simp only [List.foldl_nil]
    constructor
    · intro h; exact .inr ⟨fun p hp => absurd hp List.not_mem_nil, h⟩
    · rintro (⟨p, hp, -⟩ | ⟨-, h⟩)
      · exact absurd hp List.not_mem_nil
      · exact h
  | cons p L ih =>
    intro m0 hd x v
    simp only [List.map_cons, List.pairwise_cons] at hd
    simp only [List.foldl_cons]
    rw [ih _ hd.2 x v]
    simp only [insP]
    by_cases hp : p.1 = x
    · subst hp
      rw [treeMap_insert_self]
      have hL : ∀ q ∈ L, q.1 ≠ p.1 := fun q hq e => hd.1 q.1 (List.mem_map_of_mem hq) e.symm
      constructor
      · rintro (⟨q, hq, hqx, -⟩ | ⟨-, h⟩)
        · exact absurd hqx (hL q hq)
        · cases h; exact .inl ⟨p, by simp, rfl, rfl⟩
      · rintro (⟨q, hq, hqx, rfl⟩ | ⟨h, -⟩)
        · rcases List.mem_cons.1 hq with rfl | hq
          · exact .inr ⟨hL, rfl⟩
          · exact absurd hqx (hL q hq)
        · exact absurd rfl (h p (by simp))
    · rw [treeMap_insert_ne _ _ hp]
      constructor
      · rintro (⟨q, hq, hqx, rfl⟩ | ⟨h, h'⟩)
        · exact .inl ⟨q, List.mem_cons_of_mem _ hq, hqx, rfl⟩
        · refine .inr ⟨fun q hq => ?_, h'⟩
          rcases List.mem_cons.1 hq with rfl | hq
          · exact hp
          · exact h q hq
      · rintro (⟨q, hq, hqx, rfl⟩ | ⟨h, h'⟩)
        · rcases List.mem_cons.1 hq with rfl | hq
          · exact absurd hqx hp
          · exact .inl ⟨q, hq, hqx, rfl⟩
        · exact .inr ⟨fun q hq => h q (List.mem_cons_of_mem _ hq), h'⟩

/-! ## The pairs -/

/-- The names a member contributes: its own, then its constructors'. -/
def keysOf (m : MutConst) : List Name := m.name :: m.ctors.toList.map (·.cnst.name)

/-- The member and constructor names are pairwise distinct (Lean's names are
unique). -/
def KeysDistinct (ms : List MutConst) : Prop := (ms.flatMap keysOf).Nodup

theorem KeysDistinct.perm {ms ms' : List MutConst} (h : ms.Perm ms') (hk : KeysDistinct ms) :
    KeysDistinct ms' :=
  (List.Perm.flatMap_right keysOf h).nodup_iff.1 hk

theorem map_zipIdx_fst {β γ : Type} (f : β → γ) :
    ∀ (l : List β) (n : Nat), (l.zipIdx n).map (fun q => f q.1) = l.map f
  | [], _ => rfl
  | b :: l, n => by simp only [List.zipIdx_cons, List.map_cons]; rw [map_zipIdx_fst f l (n + 1)]

theorem keys_pairsOf (j i : Nat) (C : List MutConst) :
    (pairsOf j i C).map (·.1) = C.flatMap keysOf := by
  induction C with
  | nil => rfl
  | cons m C ih =>
    simp only [pairsOf, List.flatMap_cons, List.map_append] at ih ⊢
    rw [ih]
    simp only [List.map_cons, List.map_map, keysOf, List.cons_append]
    congr 2
    exact map_zipIdx_fst (fun c : ConstructorVal => c.cnst.name) _ 0

/-- The base of class `j`'s constructor slots, past the earlier classes'. -/
def offs (cls : List (List MutConst)) (j : Nat) : Nat := sumMaxC (cls.take j)

theorem offs_zero (cls : List (List MutConst)) : offs cls 0 = 0 := by simp [offs, sumMaxC]

theorem offs_cons_succ (C : List MutConst) (rest : List (List MutConst)) (j : Nat) :
    offs (C :: rest) (j + 1) = maxC C + offs rest j := by simp [offs, sumMaxC]

theorem keys_ctxPairs : ∀ (cls : List (List MutConst)) (n i : Nat),
    (ctxPairs cls n i).map (·.1) = cls.flatten.flatMap keysOf
  | [], _, _ => rfl
  | C :: rest, n, i => by
    simp only [ctxPairs, List.map_append, keys_pairsOf, keys_ctxPairs rest, List.flatten_cons,
      List.flatMap_append]

theorem mem_pairsOf {p : Name × Nat} {j i : Nat} {C : List MutConst} :
    p ∈ pairsOf j i C ↔ ∃ m ∈ C, p = (m.name, j) ∨
      ∃ (k : Nat) (c : ConstructorVal), m.ctors[k]? = some c ∧ p = (c.cnst.name, i + k) := by
  simp only [pairsOf, List.mem_flatMap, List.mem_cons, List.mem_map]
  refine exists_congr fun m => and_congr_right fun _ => or_congr_right ?_
  constructor
  · rintro ⟨⟨c, k⟩, hq, rfl⟩
    have := List.mem_zipIdx_iff_getElem?.1 hq
    simp only [Array.getElem?_toList] at this
    exact ⟨k, c, this, rfl⟩
  · rintro ⟨k, c, hc, rfl⟩
    exact ⟨(c, k), List.mem_zipIdx_iff_getElem?.2 (by simpa [Array.getElem?_toList] using hc), rfl⟩

theorem mem_ctxPairs : ∀ (cls : List (List MutConst)) (n i : Nat) (p : Name × Nat),
    p ∈ ctxPairs cls n i ↔ ∃ (j : Nat) (C : List MutConst) (m : MutConst), cls[j]? = some C ∧ m ∈ C ∧
      (p = (m.name, n + j) ∨ ∃ (k : Nat) (c : ConstructorVal), m.ctors[k]? = some c ∧
        p = (c.cnst.name, i + offs cls j + k))
  | [], n, i, p => by
    simp only [ctxPairs, List.not_mem_nil, false_iff]
    rintro ⟨j, C, m, hC, -⟩
    rw [List.getElem?_nil] at hC; cases hC
  | C :: rest, n, i, p => by
    simp only [ctxPairs, List.mem_append, mem_pairsOf, mem_ctxPairs rest (n + 1) (i + maxC C) p]
    constructor
    · rintro (⟨m, hm, h⟩ | ⟨j, D, m, hD, hm, h⟩)
      · refine ⟨0, C, m, rfl, hm, ?_⟩
        rcases h with h | ⟨k, c, hc, h⟩
        · exact .inl (by rw [h, Nat.add_zero])
        · exact .inr ⟨k, c, hc, by rw [h, offs_zero, Nat.add_zero]⟩
      · refine ⟨j + 1, D, m, by rw [List.getElem?_cons_succ]; exact hD, hm, ?_⟩
        rcases h with h | ⟨k, c, hc, h⟩
        · exact .inl (by rw [h]; congr 1; omega)
        · exact .inr ⟨k, c, hc, by rw [h, offs_cons_succ]; congr 1; omega⟩
    · rintro ⟨j, D, m, hD, hm, h⟩
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hD; subst hD
        refine .inl ⟨m, hm, ?_⟩
        rcases h with h | ⟨k, c, hc, h⟩
        · exact .inl (by rw [h, Nat.add_zero])
        · exact .inr ⟨k, c, hc, by rw [h, offs_zero, Nat.add_zero]⟩
      | succ j =>
        simp only [List.getElem?_cons_succ] at hD
        refine .inr ⟨j, D, m, hD, hm, ?_⟩
        rcases h with h | ⟨k, c, hc, h⟩
        · exact .inl (by rw [h]; congr 1; omega)
        · exact .inr ⟨k, c, hc, by rw [h, offs_cons_succ]; congr 1; omega⟩

/-! ## Values of the context -/

theorem default_getElem? (x : Name) : (default : MutCtx)[x]? = none := by
  show (∅ : MutCtx)[x]? = none
  exact Std.TreeMap.getElem?_emptyc

/-- Distinct keys, as a pairwise statement. -/
theorem KeysDistinct.ne {ms : List MutConst} (hk : KeysDistinct ms) :
    (ms.flatMap keysOf).Pairwise (· ≠ ·) := hk

section
variable {cls : List (List MutConst)} (hk : KeysDistinct cls.flatten)
include hk

theorem ctx_lookup (x : Name) (v : Nat) :
    (MutConst.ctx cls)[x]? = some v ↔ ∃ p ∈ ctxPairs cls 0 cls.length, p.1 = x ∧ p.2 = v := by
  rw [ctx_fold, foldl_insP_getElem? _ _ (by rw [keys_ctxPairs]; exact hk.ne), default_getElem?]
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact h
    · cases h
  · exact .inl

theorem ctx_member {j : Nat} {C : List MutConst} {m : MutConst} (hC : cls[j]? = some C)
    (hm : m ∈ C) : (MutConst.ctx cls)[m.name]? = some j :=
  (ctx_lookup hk _ _).2 ⟨(m.name, j), (mem_ctxPairs cls 0 _ _).2 ⟨j, C, m, hC, hm, .inl (by simp)⟩,
    rfl, rfl⟩

theorem ctx_ctor {j : Nat} {C : List MutConst} {m : MutConst} (hC : cls[j]? = some C)
    (hm : m ∈ C) {k : Nat} {c : ConstructorVal} (hc : m.ctors[k]? = some c) :
    (MutConst.ctx cls)[c.cnst.name]? = some (cls.length + offs cls j + k) :=
  (ctx_lookup hk _ _).2 ⟨(c.cnst.name, cls.length + offs cls j + k),
    (mem_ctxPairs cls 0 _ _).2 ⟨j, C, m, hC, hm, .inr ⟨k, c, hc, rfl⟩⟩, rfl, rfl⟩

theorem ctx_val {x : Name} {v : Nat} (h : (MutConst.ctx cls)[x]? = some v) :
    ∃ (j : Nat) (C : List MutConst) (m : MutConst), cls[j]? = some C ∧ m ∈ C ∧
      ((m.name = x ∧ v = j) ∨ ∃ (k : Nat) (c : ConstructorVal), m.ctors[k]? = some c ∧
        c.cnst.name = x ∧ v = cls.length + offs cls j + k) := by
  obtain ⟨p, hp, hpx, rfl⟩ := (ctx_lookup hk x v).1 h
  obtain ⟨j, C, m, hC, hm, hp'⟩ := (mem_ctxPairs cls 0 _ p).1 hp
  refine ⟨j, C, m, hC, hm, ?_⟩
  rcases hp' with rfl | ⟨k, c, hc, rfl⟩
  · exact .inl ⟨hpx, by simp⟩
  · exact .inr ⟨k, c, hc, hpx, rfl⟩

end

/-- The names in the context are the member and constructor names. -/
theorem ctx_dom (cls : List (List MutConst)) (x : Name) :
    ((MutConst.ctx cls)[x]?).isSome = true ↔ x ∈ cls.flatten.flatMap keysOf := by
  have key : ∀ (L : List (Name × Nat)) (m0 : MutCtx),
      ((L.foldl insP m0)[x]?).isSome = true ↔ (x ∈ L.map (·.1) ∨ (m0[x]?).isSome = true) := by
    intro L
    induction L with
    | nil => intro m0; simp
    | cons p L ih =>
      intro m0
      simp only [List.foldl_cons, List.map_cons, List.mem_cons]
      rw [ih]
      simp only [insP]
      by_cases hp : p.1 = x
      · subst hp; simp
      · rw [treeMap_insert_ne _ _ hp]
        constructor
        · rintro (h | h)
          · exact .inl (.inr h)
          · exact .inr h
        · rintro ((h | h) | h)
          · exact absurd h.symm hp
          · exact .inl h
          · exact .inr h
  rw [ctx_fold, key, keys_ctxPairs, default_getElem?]
  simp
/-! ## Constructor slots are disjoint across classes -/

theorem maxC_ge {C : List MutConst} {m : MutConst} (hm : m ∈ C) : m.ctors.size ≤ maxC C := by
  unfold maxC
  induction C with
  | nil => cases hm
  | cons x C ih =>
    simp only [List.foldl_cons, Nat.zero_max]
    rw [foldl_max]
    rcases List.mem_cons.1 hm with rfl | hm
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (by simpa [maxC] using ih hm) (Nat.le_max_right _ _)

theorem offs_succ : ∀ (cls : List (List MutConst)) (j : Nat) (C : List MutConst), cls[j]? = some C →
    offs cls (j + 1) = offs cls j + maxC C
  | [], _, _, h => by cases h
  | D :: rest, 0, C, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    simp [offs, sumMaxC]
  | D :: rest, j + 1, C, h => by
    simp only [List.getElem?_cons_succ] at h
    rw [offs_cons_succ, offs_cons_succ, offs_succ rest j C h]; omega

theorem offs_mono (cls : List (List MutConst)) : ∀ {j₁ j₂ : Nat}, j₁ ≤ j₂ → offs cls j₁ ≤ offs cls j₂ := by
  intro j₁ j₂ h
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    rename_i j _
    have : offs cls j ≤ offs cls (j + 1) := by
      unfold offs
      rcases Nat.lt_or_ge j cls.length with hj | hj
      · rw [List.take_add_one, List.getElem?_eq_getElem hj]
        have : ∀ (a b : List (List MutConst)), sumMaxC (a ++ b) = sumMaxC a + sumMaxC b := by
          intro a b; induction a with
          | nil => simp [sumMaxC]
          | cons x a ih' => simp only [List.cons_append, sumMaxC, ih']; omega
        simp only [Option.toList_some, this]; omega
      · rw [List.take_of_length_le hj, List.take_of_length_le (by omega)]; exact Nat.le_refl _
    exact Nat.le_trans ih this

theorem slot_disjoint {cls : List (List MutConst)} {j₁ j₂ : Nat} {C₁ C₂ : List MutConst}
    (h₁ : cls[j₁]? = some C₁) (h₂ : cls[j₂]? = some C₂) {k₁ k₂ : Nat} (hk₁ : k₁ < maxC C₁)
    (hk₂ : k₂ < maxC C₂) (h : offs cls j₁ + k₁ = offs cls j₂ + k₂) : j₁ = j₂ ∧ k₁ = k₂ := by
  rcases Nat.lt_trichotomy j₁ j₂ with hl | rfl | hl
  · have := offs_mono cls (Nat.succ_le_of_lt hl); rw [offs_succ cls j₁ C₁ h₁] at this; omega
  · exact ⟨rfl, by omega⟩
  · have := offs_mono cls (Nat.succ_le_of_lt hl); rw [offs_succ cls j₂ C₂ h₂] at this; omega

end Ix.CompileCert.Canon
